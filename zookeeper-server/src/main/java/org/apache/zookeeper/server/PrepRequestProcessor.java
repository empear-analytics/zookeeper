/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.zookeeper.server;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.StringReader;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;
import org.apache.jute.BinaryOutputArchive;
import org.apache.jute.Record;
import org.apache.zookeeper.CreateMode;
import org.apache.zookeeper.DeleteContainerRequest;
import org.apache.zookeeper.KeeperException;
import org.apache.zookeeper.KeeperException.BadArgumentsException;
import org.apache.zookeeper.KeeperException.Code;
import org.apache.zookeeper.MultiOperationRecord;
import org.apache.zookeeper.Op;
import org.apache.zookeeper.ZooDefs;
import org.apache.zookeeper.ZooDefs.OpCode;
import org.apache.zookeeper.common.PathUtils;
import org.apache.zookeeper.common.StringUtils;
import org.apache.zookeeper.common.Time;
import org.apache.zookeeper.data.ACL;
import org.apache.zookeeper.data.Id;
import org.apache.zookeeper.data.StatPersisted;
import org.apache.zookeeper.proto.CheckVersionRequest;
import org.apache.zookeeper.proto.CreateRequest;
import org.apache.zookeeper.proto.CreateTTLRequest;
import org.apache.zookeeper.proto.DeleteRequest;
import org.apache.zookeeper.proto.ReconfigRequest;
import org.apache.zookeeper.proto.SetACLRequest;
import org.apache.zookeeper.proto.SetDataRequest;
import org.apache.zookeeper.server.ZooKeeperServer.ChangeRecord;
import org.apache.zookeeper.server.ZooKeeperServer.PrecalculatedDigest;
import org.apache.zookeeper.server.auth.ProviderRegistry;
import org.apache.zookeeper.server.auth.ServerAuthenticationProvider;
import org.apache.zookeeper.server.quorum.LeaderZooKeeperServer;
import org.apache.zookeeper.server.quorum.QuorumPeer.QuorumServer;
import org.apache.zookeeper.server.quorum.QuorumPeerConfig;
import org.apache.zookeeper.server.quorum.QuorumPeerConfig.ConfigException;
import org.apache.zookeeper.server.quorum.flexible.QuorumMaj;
import org.apache.zookeeper.server.quorum.flexible.QuorumOracleMaj;
import org.apache.zookeeper.server.quorum.flexible.QuorumVerifier;
import org.apache.zookeeper.txn.CheckVersionTxn;
import org.apache.zookeeper.txn.CloseSessionTxn;
import org.apache.zookeeper.txn.CreateContainerTxn;
import org.apache.zookeeper.txn.CreateSessionTxn;
import org.apache.zookeeper.txn.CreateTTLTxn;
import org.apache.zookeeper.txn.CreateTxn;
import org.apache.zookeeper.txn.DeleteTxn;
import org.apache.zookeeper.txn.ErrorTxn;
import org.apache.zookeeper.txn.MultiTxn;
import org.apache.zookeeper.txn.SetACLTxn;
import org.apache.zookeeper.txn.SetDataTxn;
import org.apache.zookeeper.txn.Txn;
import org.apache.zookeeper.txn.TxnDigest;
import org.apache.zookeeper.txn.TxnHeader;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This request processor is generally at the start of a RequestProcessor
 * change. It sets up any transactions associated with requests that change the
 * state of the system. It counts on ZooKeeperServer to update
 * outstandingRequests, so that it can take into account transactions that are
 * in the queue to be applied when generating a transaction.
 */
public class PrepRequestProcessor extends ZooKeeperCriticalThread implements RequestProcessor {

    private static final Logger LOG = LoggerFactory.getLogger(PrepRequestProcessor.class);

    /**
     * this is only for testing purposes.
     * should never be used otherwise
     */
    private static boolean failCreate = false;

    LinkedBlockingQueue<Request> submittedRequests = new LinkedBlockingQueue<>();

    private final RequestProcessor nextProcessor;
    private final boolean digestEnabled;
    private DigestCalculator digestCalculator;

    ZooKeeperServer zks;

    public enum DigestOpCode {
        NOOP, ADD, REMOVE, UPDATE;
    }

    public PrepRequestProcessor(ZooKeeperServer zks, RequestProcessor nextProcessor) {
        super(
            "ProcessThread(sid:" + zks.getServerId()
            + " cport:" + zks.getClientPort()
            + "):", zks.getZooKeeperServerListener());
        this.nextProcessor = nextProcessor;
        this.zks = zks;
        this.digestEnabled = ZooKeeperServer.isDigestEnabled();
        if (this.digestEnabled) {
            this.digestCalculator = new DigestCalculator();
        }
    }

    /**
     * method for tests to set failCreate
     * @param b
     */
    public static void setFailCreate(boolean b) {
        failCreate = b;
    }
   

    private ChangeRecord getOutstandingChange(String path) {
        synchronized (zks.outstandingChanges) {
            return zks.outstandingChangesForPath.get(path);
        }
    }

    protected void addChangeRecord(ChangeRecord c) {
        synchronized (zks.outstandingChanges) {
            zks.outstandingChanges.add(c);
            zks.outstandingChangesForPath.put(c.path, c);
            ServerMetrics.getMetrics().OUTSTANDING_CHANGES_QUEUED.add(1);
        }
    }

    /**
     * Grab current pending change records for each op in a multi-op.
     *
     * This is used inside MultiOp error code path to rollback in the event
     * of a failed multi-op.
     *
     * @param multiRequest
     * @return a map that contains previously existed records that probably need to be
     *         rolled back in any failure.
     */
    
    /**
     * Rollback pending changes records from a failed multi-op.
     *
     * If a multi-op fails, we can't leave any invalid change records we created
     * around. We also need to restore their prior value (if any) if their prior
     * value is still valid.
     *
     * @param zxid
     * @param pendingChangeRecords
     */
    
    /**
     * Performs basic validation of a path for a create request.
     * Throws if the path is not valid and returns the parent path.
     * @throws BadArgumentsException
     */
    private String validatePathForCreate(String path, long sessionId) throws BadArgumentsException {
        int lastSlash = path.lastIndexOf('/');
        if (lastSlash == -1 || path.indexOf('\0') != -1 || failCreate) {
            LOG.info("Invalid path {} with session 0x{}", path, Long.toHexString(sessionId));
            throw new KeeperException.BadArgumentsException(path);
        }
        return path.substring(0, lastSlash);
    }

    private void pRequest2TxnCreate(int type, Request request, Record record) throws IOException, KeeperException {
        int flags;
        String path;
        List<ACL> acl;
        byte[] data;
        long ttl;
        if (type == OpCode.createTTL) {
            CreateTTLRequest createTtlRequest = (CreateTTLRequest) record;
            flags = createTtlRequest.getFlags();
            path = createTtlRequest.getPath();
            acl = createTtlRequest.getAcl();
            data = createTtlRequest.getData();
            ttl = createTtlRequest.getTtl();
        } else {
            CreateRequest createRequest = (CreateRequest) record;
            flags = createRequest.getFlags();
            path = createRequest.getPath();
            acl = createRequest.getAcl();
            data = createRequest.getData();
            ttl = -1;
        }
        CreateMode createMode = CreateMode.fromFlag(flags);
        validateCreateRequest(path, createMode, request, ttl);
        String parentPath = validatePathForCreate(path, request.sessionId);

        List<ACL> listACL = fixupACL(path, request.authInfo, acl);
        ChangeRecord parentRecord = getRecordForPath(parentPath);

        zks.checkACL(request.cnxn, parentRecord.acl, ZooDefs.Perms.CREATE, request.authInfo, path, listACL);
        int parentCVersion = parentRecord.stat.getCversion();
        if (createMode.isSequential()) {
            path = path + String.format(Locale.ENGLISH, "%010d", parentCVersion);
        }
        validatePath(path, request.sessionId);
        try {
            if (getRecordForPath(path) != null) {
                throw new KeeperException.NodeExistsException(path);
            }
        } catch (KeeperException.NoNodeException e) {
            // ignore this one
        }
        boolean ephemeralParent = EphemeralType.get(parentRecord.stat.getEphemeralOwner()) == EphemeralType.NORMAL;
        if (ephemeralParent) {
            throw new KeeperException.NoChildrenForEphemeralsException(path);
        }
        int newCversion = parentRecord.stat.getCversion() + 1;
        zks.checkQuota(path, null, data, OpCode.create);
        if (type == OpCode.createContainer) {
            request.setTxn(new CreateContainerTxn(path, data, listACL, newCversion));
        } else if (type == OpCode.createTTL) {
            request.setTxn(new CreateTTLTxn(path, data, listACL, newCversion, ttl));
        } else {
            request.setTxn(new CreateTxn(path, data, listACL, createMode.isEphemeral(), newCversion));
        }

        TxnHeader hdr = request.getHdr();
        long ephemeralOwner = 0;
        if (createMode.isContainer()) {
            ephemeralOwner = EphemeralType.CONTAINER_EPHEMERAL_OWNER;
        } else if (createMode.isTTL()) {
            ephemeralOwner = EphemeralType.TTL.toEphemeralOwner(ttl);
        } else if (createMode.isEphemeral()) {
            ephemeralOwner = request.sessionId;
        }
        StatPersisted s = DataTree.createStat(hdr.getZxid(), hdr.getTime(), ephemeralOwner);
        parentRecord = parentRecord.duplicate(request.getHdr().getZxid());
        parentRecord.childCount++;
        parentRecord.stat.setCversion(newCversion);
        parentRecord.stat.setPzxid(request.getHdr().getZxid());
        parentRecord.precalculatedDigest = precalculateDigest(
                DigestOpCode.UPDATE, parentPath, parentRecord.data, parentRecord.stat);
        addChangeRecord(parentRecord);
        ChangeRecord nodeRecord = new ChangeRecord(
                request.getHdr().getZxid(), path, s, 0, listACL);
        nodeRecord.data = data;
        nodeRecord.precalculatedDigest = precalculateDigest(
                DigestOpCode.ADD, path, nodeRecord.data, s);
        setTxnDigest(request, nodeRecord.precalculatedDigest);
        addChangeRecord(nodeRecord);
    }

    private void validatePath(String path, long sessionId) throws BadArgumentsException {
        try {
            PathUtils.validatePath(path);
        } catch (IllegalArgumentException ie) {
            LOG.info("Invalid path {} with session 0x{}, reason: {}", path, Long.toHexString(sessionId), ie.getMessage());
            throw new BadArgumentsException(path);
        }
    }

    private String getParentPathAndValidate(String path) throws BadArgumentsException {
        int lastSlash = path.lastIndexOf('/');
        if (lastSlash == -1 || path.indexOf('\0') != -1 || zks.getZKDatabase().isSpecialPath(path)) {
            throw new BadArgumentsException(path);
        }
        return path.substring(0, lastSlash);
    }

    private static int checkAndIncVersion(int currentVersion, int expectedVersion, String path) throws KeeperException.BadVersionException {
        if (expectedVersion != -1 && expectedVersion != currentVersion) {
            throw new KeeperException.BadVersionException(path);
        }
        return currentVersion + 1;
    }

    /**
     * This method will be called inside the ProcessRequestThread, which is a
     * singleton, so there will be a single thread calling this code.
     *
     * @param request
     */
    protected void pRequest(Request request) throws RequestProcessorException {
        request.setHdr(null);
        request.setTxn(null);

        if (!request.isThrottled()) {
          pRequestHelper(request);
        }

        request.zxid = zks.getZxid();
        long timeFinishedPrepare = Time.currentElapsedTime();
        ServerMetrics.getMetrics().PREP_PROCESS_TIME.add(timeFinishedPrepare - request.prepStartTime);
        nextProcessor.processRequest(request);
        ServerMetrics.getMetrics().PROPOSAL_PROCESS_TIME.add(Time.currentElapsedTime() - timeFinishedPrepare);
    }

    /**
     * This method is a helper to pRequest method
     */
    private void pRequestHelper(Request request) {
        try {
            switch (request.type) {
            case OpCode.createContainer:
            case OpCode.create:
            case OpCode.create2:
                CreateRequest create2Request = request.readRequestRecord(CreateRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, create2Request);
                break;
            case OpCode.createTTL:
                CreateTTLRequest createTtlRequest = request.readRequestRecord(CreateTTLRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, createTtlRequest);
                break;
            case OpCode.deleteContainer:
                DeleteContainerRequest deleteContainerRequest = request.readRequestRecord(DeleteContainerRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, deleteContainerRequest);
                break;
            case OpCode.delete:
                DeleteRequest deleteRequest = request.readRequestRecord(DeleteRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, deleteRequest);
                break;
            case OpCode.setData:
                SetDataRequest setDataRequest = request.readRequestRecord(SetDataRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, setDataRequest);
                break;
            case OpCode.reconfig:
                ReconfigRequest reconfigRequest = request.readRequestRecord(ReconfigRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, reconfigRequest);
                break;
            case OpCode.setACL:
                SetACLRequest setAclRequest = request.readRequestRecord(SetACLRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, setAclRequest);
                break;
            case OpCode.check:
                CheckVersionRequest checkRequest = request.readRequestRecord(CheckVersionRequest::new);
                pRequest2Txn(request.type, zks.getNextZxid(), request, checkRequest);
                break;
            case OpCode.multi:
                MultiOperationRecord multiRequest;
                try {
                    multiRequest = request.readRequestRecord(MultiOperationRecord::new);
                } catch (IOException e) {
                    request.setHdr(new TxnHeader(request.sessionId, request.cxid, zks.getNextZxid(), Time.currentWallTime(), OpCode.multi));
                    throw e;
                }
                List<Txn> txns = new ArrayList<>();
                //Each op in a multi-op must have the same zxid!
                long zxid = zks.getNextZxid();
                KeeperException ke = null;

                //Store off current pending change records in case we need to rollback
                Map<String, ChangeRecord> pendingChanges = getPendingChanges(multiRequest);
                request.setHdr(new TxnHeader(request.sessionId, request.cxid, zxid,
                        Time.currentWallTime(), request.type));

                for (Op op : multiRequest) {
                    Record subrequest = op.toRequestRecord();
                    int type;
                    Record txn;

                    /* If we've already failed one of the ops, don't bother
                     * trying the rest as we know it's going to fail and it
                     * would be confusing in the logfiles.
                     */
                    if (ke != null) {
                        type = OpCode.error;
                        txn = new ErrorTxn(Code.RUNTIMEINCONSISTENCY.intValue());
                    } else {
                        /* Prep the request and convert to a Txn */
                        try {
                            pRequest2Txn(op.getType(), zxid, request, subrequest);
                            type = op.getType();
                            txn = request.getTxn();
                        } catch (KeeperException e) {
                            ke = e;
                            type = OpCode.error;
                            txn = new ErrorTxn(e.code().intValue());

                            if (e.code().intValue() > Code.APIERROR.intValue()) {
                                LOG.info("Got user-level KeeperException when processing {} aborting"
                                         + " remaining multi ops. Error Path:{} Error:{}",
                                         request.toString(),
                                         e.getPath(),
                                         e.getMessage());
                            }

                            request.setException(e);

                            /* Rollback change records from failed multi-op */
                            rollbackPendingChanges(zxid, pendingChanges);
                        }
                    }

                    // TODO: I don't want to have to serialize it here and then
                    //       immediately deserialize in next processor. But I'm
                    //       not sure how else to get the txn stored into our list.
                    try (ByteArrayOutputStream baos = new ByteArrayOutputStream()) {
                        BinaryOutputArchive boa = BinaryOutputArchive.getArchive(baos);
                        txn.serialize(boa, "request");
                        ByteBuffer bb = ByteBuffer.wrap(baos.toByteArray());
                        txns.add(new Txn(type, bb.array()));
                    }
                }

                request.setTxn(new MultiTxn(txns));
                if (digestEnabled) {
                    setTxnDigest(request);
                }

                break;

            //create/close session don't require request record
            case OpCode.createSession:
            case OpCode.closeSession:
                if (!request.isLocalSession()) {
                    pRequest2Txn(request.type, zks.getNextZxid(), request, null);
                }
                break;

            //All the rest don't need to create a Txn - just verify session
            case OpCode.sync:
            case OpCode.exists:
            case OpCode.getData:
            case OpCode.getACL:
            case OpCode.getChildren:
            case OpCode.getAllChildrenNumber:
            case OpCode.getChildren2:
            case OpCode.ping:
            case OpCode.setWatches:
            case OpCode.setWatches2:
            case OpCode.checkWatches:
            case OpCode.removeWatches:
            case OpCode.getEphemerals:
            case OpCode.multiRead:
            case OpCode.addWatch:
            case OpCode.whoAmI:
                zks.sessionTracker.checkSession(request.sessionId, request.getOwner());
                break;
            default:
                LOG.warn("unknown type {}", request.type);
                break;
            }
        } catch (KeeperException e) {
            if (request.getHdr() != null) {
                request.getHdr().setType(OpCode.error);
                request.setTxn(new ErrorTxn(e.code().intValue()));
            }

            if (e.code().intValue() > Code.APIERROR.intValue()) {
                LOG.info(
                    "Got user-level KeeperException when processing {} Error Path:{} Error:{}",
                    request.toString(),
                    e.getPath(),
                    e.getMessage());
            }
            request.setException(e);
        } catch (Exception e) {
            // log at error level as we are returning a marshalling
            // error to the user
            LOG.error("Failed to process {}", request, e);
            String digest = request.requestDigest();
            LOG.error("Dumping request buffer for request type {}: 0x{}", Request.op2String(request.type), digest);
            if (request.getHdr() == null) {
                request.setHdr(new TxnHeader(request.sessionId, request.cxid, zks.getZxid(), Time.currentWallTime(), request.type));
            }

            request.getHdr().setType(OpCode.error);
            request.setTxn(new ErrorTxn(Code.MARSHALLINGERROR.intValue()));
        }
    }

    private static List<ACL> removeDuplicates(final List<ACL> acls) {
        if (acls == null || acls.isEmpty()) {
            return Collections.emptyList();
        }

        // This would be done better with a Set but ACL hashcode/equals do not
        // allow for null values
        final ArrayList<ACL> retval = new ArrayList<>(acls.size());
        for (final ACL acl : acls) {
            if (!retval.contains(acl)) {
                retval.add(acl);
            }
        }
        return retval;
    }

    private void validateCreateRequest(String path, CreateMode createMode, Request request, long ttl) throws KeeperException {
        if (createMode.isTTL() && !EphemeralType.extendedEphemeralTypesEnabled()) {
            throw new KeeperException.UnimplementedException();
        }
        try {
            EphemeralType.validateTTL(createMode, ttl);
        } catch (IllegalArgumentException e) {
            throw new BadArgumentsException(path);
        }
        if (createMode.isEphemeral()) {
            // Exception is set when local session failed to upgrade
            // so we just need to report the error
            if (request.getException() != null) {
                throw request.getException();
            }
            zks.sessionTracker.checkGlobalSession(request.sessionId, request.getOwner());
        } else {
            zks.sessionTracker.checkSession(request.sessionId, request.getOwner());
        }
    }

    /**
     * This method checks out the acl making sure it isn't null or empty,
     * it has valid schemes and ids, and expanding any relative ids that
     * depend on the requestor's authentication information.
     *
     * @param authInfo list of ACL IDs associated with the client connection
     * @param acls list of ACLs being assigned to the node (create or setACL operation)
     * @return verified and expanded ACLs
     * @throws KeeperException.InvalidACLException
     */
    public static List<ACL> fixupACL(String path, List<Id> authInfo, List<ACL> acls) throws KeeperException.InvalidACLException {
        // check for well formed ACLs
        // This resolves https://issues.apache.org/jira/browse/ZOOKEEPER-1877
        List<ACL> uniqacls = removeDuplicates(acls);
        if (uniqacls == null || uniqacls.size() == 0) {
            throw new KeeperException.InvalidACLException(path);
        }
        List<ACL> rv = new ArrayList<>();
        for (ACL a : uniqacls) {
            LOG.debug("Processing ACL: {}", a);
            if (a == null) {
                throw new KeeperException.InvalidACLException(path);
            }
            Id id = a.getId();
            if (id == null || id.getScheme() == null) {
                throw new KeeperException.InvalidACLException(path);
            }
            if (id.getScheme().equals("world") && id.getId().equals("anyone")) {
                rv.add(a);
            } else if (id.getScheme().equals("auth")) {
                // This is the "auth" id, so we have to expand it to the
                // authenticated ids of the requestor
                boolean authIdValid = false;
                for (Id cid : authInfo) {
                    ServerAuthenticationProvider ap = ProviderRegistry.getServerProvider(cid.getScheme());
                    if (ap == null) {
                        LOG.error("Missing AuthenticationProvider for {}", cid.getScheme());
                    } else if (ap.isAuthenticated()) {
                        authIdValid = true;
                        rv.add(new ACL(a.getPerms(), cid));
                    }
                }
                if (!authIdValid) {
                    throw new KeeperException.InvalidACLException(path);
                }
            } else {
                ServerAuthenticationProvider ap = ProviderRegistry.getServerProvider(id.getScheme());
                if (ap == null || !ap.isValid(id.getId())) {
                    throw new KeeperException.InvalidACLException(path);
                }
                rv.add(a);
            }
        }
        return rv;
    }

    public void processRequest(Request request) {
        request.prepQueueStartTime = Time.currentElapsedTime();
        submittedRequests.add(request);
        ServerMetrics.getMetrics().PREP_PROCESSOR_QUEUED.add(1);
    }

    public void shutdown() {
        LOG.info("Shutting down");
        submittedRequests.clear();
        submittedRequests.add(Request.requestOfDeath);
        nextProcessor.shutdown();
    }

    /**
     * Calculate the node digest and tree digest after the change.
     *
     * @param type the type of operations about the digest change
     * @param path the path of the node
     * @param data the data of the node
     * @param s the stat of the node
     *
     * @return PrecalculatedDigest the pair of node and tree digest
     */
    private PrecalculatedDigest precalculateDigest(DigestOpCode type, String path,
            byte[] data, StatPersisted s) throws KeeperException.NoNodeException {

        if (!digestEnabled) {
            return null;
        }

        long prevNodeDigest;
        long newNodeDigest;

        switch (type) {
            case ADD:
                prevNodeDigest = 0;
                newNodeDigest = digestCalculator.calculateDigest(path, data, s);
                break;
            case REMOVE:
                prevNodeDigest = getRecordForPath(path).precalculatedDigest.nodeDigest;
                newNodeDigest = 0;
                break;
            case UPDATE:
                prevNodeDigest = getRecordForPath(path).precalculatedDigest.nodeDigest;
                newNodeDigest = digestCalculator.calculateDigest(path, data, s);
                break;
            case NOOP:
                newNodeDigest = prevNodeDigest = 0;
                break;
            default:
                return null;
        }
        long treeDigest = getCurrentTreeDigest() - prevNodeDigest + newNodeDigest;
        return new PrecalculatedDigest(newNodeDigest, treeDigest);
    }

    private PrecalculatedDigest precalculateDigest(
            DigestOpCode type, String path) throws KeeperException.NoNodeException {
        return precalculateDigest(type, path, null, null);
    }

    /**
     * Query the current tree digest from DataTree or outstandingChanges list.
     *
     * @return current tree digest
     */
    private long getCurrentTreeDigest() {
        long digest;
        synchronized (zks.outstandingChanges) {
            if (zks.outstandingChanges.isEmpty()) {
                digest = zks.getZKDatabase().getDataTree().getTreeDigest();
                LOG.debug("Digest got from data tree is: {}", digest);
            } else {
                digest = zks.outstandingChanges.peekLast().precalculatedDigest.treeDigest;
                LOG.debug("Digest got from outstandingChanges is: {}", digest);
            }
        }
        return digest;
    }

    private void setTxnDigest(Request request) {
        request.setTxnDigest(new TxnDigest(digestCalculator.getDigestVersion(), getCurrentTreeDigest()));
    }

    private void setTxnDigest(Request request, PrecalculatedDigest preCalculatedDigest) {
        if (preCalculatedDigest == null) {
            return;
        }
        request.setTxnDigest(new TxnDigest(digestCalculator.getDigestVersion(), preCalculatedDigest.treeDigest));
    }
}
