/**
 *
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 *
 */

package org.apache.bookkeeper.bookie;

import static org.apache.bookkeeper.bookie.BookKeeperServerStats.JOURNAL_MEMORY_MAX;
import static org.apache.bookkeeper.bookie.BookKeeperServerStats.JOURNAL_MEMORY_USED;
import static org.apache.bookkeeper.bookie.BookKeeperServerStats.JOURNAL_SCOPE;
import static org.apache.bookkeeper.bookie.BookKeeperServerStats.LD_INDEX_SCOPE;
import static org.apache.bookkeeper.bookie.BookKeeperServerStats.LD_LEDGER_SCOPE;
import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.Lists;
import io.netty.buffer.ByteBuf;
import io.netty.buffer.ByteBufAllocator;
import io.netty.buffer.PooledByteBufAllocator;
import io.netty.buffer.Unpooled;
import io.netty.buffer.UnpooledByteBufAllocator;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.URI;
import java.net.UnknownHostException;
import java.nio.ByteBuffer;
import java.nio.file.FileStore;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.PrimitiveIterator.OfLong;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import org.apache.bookkeeper.bookie.BookieException.BookieIllegalOpException;
import org.apache.bookkeeper.bookie.BookieException.CookieNotFoundException;
import org.apache.bookkeeper.bookie.BookieException.DiskPartitionDuplicationException;
import org.apache.bookkeeper.bookie.BookieException.InvalidCookieException;
import org.apache.bookkeeper.bookie.BookieException.MetadataStoreException;
import org.apache.bookkeeper.bookie.BookieException.UnknownBookieIdException;
import org.apache.bookkeeper.bookie.CheckpointSource.Checkpoint;
import org.apache.bookkeeper.bookie.Journal.JournalScanner;
import org.apache.bookkeeper.bookie.LedgerDirsManager.LedgerDirsListener;
import org.apache.bookkeeper.bookie.LedgerDirsManager.NoWritableLedgerDirException;
import org.apache.bookkeeper.bookie.stats.BookieStats;
import org.apache.bookkeeper.bookie.storage.ldb.DbLedgerStorage;
import org.apache.bookkeeper.common.util.Watcher;
import org.apache.bookkeeper.conf.ServerConfiguration;
import org.apache.bookkeeper.discover.BookieServiceInfo;
import org.apache.bookkeeper.discover.RegistrationManager;
import org.apache.bookkeeper.meta.LedgerManager;
import org.apache.bookkeeper.meta.LedgerManagerFactory;
import org.apache.bookkeeper.meta.MetadataBookieDriver;
import org.apache.bookkeeper.meta.MetadataDrivers;
import org.apache.bookkeeper.meta.exceptions.MetadataException;
import org.apache.bookkeeper.net.BookieId;
import org.apache.bookkeeper.net.BookieSocketAddress;
import org.apache.bookkeeper.net.DNS;
import org.apache.bookkeeper.proto.BookkeeperInternalCallbacks.WriteCallback;
import org.apache.bookkeeper.proto.SimpleBookieServiceInfoProvider;
import org.apache.bookkeeper.stats.Gauge;
import org.apache.bookkeeper.stats.NullStatsLogger;
import org.apache.bookkeeper.stats.StatsLogger;
import org.apache.bookkeeper.stats.annotations.StatsDoc;
import org.apache.bookkeeper.util.BookKeeperConstants;
import org.apache.bookkeeper.util.DiskChecker;
import org.apache.bookkeeper.util.IOUtils;
import org.apache.bookkeeper.util.MathUtils;
import org.apache.bookkeeper.util.collections.ConcurrentLongHashMap;
import org.apache.bookkeeper.versioning.Version;
import org.apache.bookkeeper.versioning.Versioned;
import org.apache.commons.configuration.ConfigurationException;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.mutable.MutableBoolean;
import org.apache.commons.lang3.tuple.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Implements a bookie.
 */
public class BookieImpl extends BookieCriticalThread implements Bookie {

    private static final Logger LOG = LoggerFactory.getLogger(Bookie.class);

    final List<File> journalDirectories;
    final ServerConfiguration conf;

    final SyncThread syncThread;
    final LedgerManagerFactory ledgerManagerFactory;
    final LedgerManager ledgerManager;
    final LedgerStorage ledgerStorage;
    final List<Journal> journals;

    final HandleFactory handles;
    final boolean entryLogPerLedgerEnabled;

    public static final long METAENTRY_ID_LEDGER_KEY = -0x1000;
    public static final long METAENTRY_ID_FENCE_KEY  = -0x2000;
    public static final long METAENTRY_ID_FORCE_LEDGER  = -0x4000;
    static final long METAENTRY_ID_LEDGER_EXPLICITLAC  = -0x8000;

    private final LedgerDirsManager ledgerDirsManager;
    protected final Supplier<BookieServiceInfo> bookieServiceInfoProvider;
    private final LedgerDirsManager indexDirsManager;
    LedgerDirsMonitor dirsMonitor;

    // Registration Manager for managing registration
    protected final MetadataBookieDriver metadataDriver;

    private int exitCode = ExitCode.OK;

    private final ConcurrentLongHashMap<byte[]> masterKeyCache = new ConcurrentLongHashMap<>();

    protected StateManager stateManager;

    // Expose Stats
    final StatsLogger statsLogger;
    private final BookieStats bookieStats;

    private final ByteBufAllocator allocator;

    private final boolean writeDataToJournal;

    @StatsDoc(
            name = JOURNAL_MEMORY_MAX,
            help = "The max amount of memory in bytes that can be used by the bookie journal"
    )
    private final Gauge<Long> journalMemoryMaxStats;

    @StatsDoc(
            name = JOURNAL_MEMORY_USED,
            help = "The actual amount of memory in bytes currently used by the bookie journal"
    )
    private final Gauge<Long> journalMemoryUsedStats;

    // Write Callback do nothing
    static class NopWriteCallback implements WriteCallback {
        @Override
        public void writeComplete(int rc, long ledgerId, long entryId,
                                  BookieId addr, Object ctx) {
            if (LOG.isDebugEnabled()) {
                LOG.debug("Finished writing entry {} @ ledger {} for {} : {}",
                        entryId, ledgerId, addr, rc);
            }
        }
    }

    public static void checkDirectoryStructure(File dir) throws IOException {
        if (!dir.exists()) {
            File parent = dir.getParentFile();
            File preV3versionFile = new File(dir.getParent(),
                    BookKeeperConstants.VERSION_FILENAME);

            final AtomicBoolean oldDataExists = new AtomicBoolean(false);
            parent.list(new FilenameFilter() {
                    @Override
                    public boolean accept(File dir, String name) {
                        if (name.endsWith(".txn") || name.endsWith(".idx") || name.endsWith(".log")) {
                            oldDataExists.set(true);
                        }
                        return true;
                    }
                });
            if (preV3versionFile.exists() || oldDataExists.get()) {
                String err = "Directory layout version is less than 3, upgrade needed";
                LOG.error(err);
                throw new IOException(err);
            }
            if (!dir.mkdirs()) {
                String err = "Unable to create directory " + dir;
                LOG.error(err);
                throw new IOException(err);
            }
        }
    }

    /**
     * Check that the environment for the bookie is correct.
     * This means that the configuration has stayed the same as the
     * first run and the filesystem structure is up to date.
     */
    private void checkEnvironment(MetadataBookieDriver metadataDriver)
            throws BookieException, IOException {
        List<File> allLedgerDirs = new ArrayList<File>(ledgerDirsManager.getAllLedgerDirs().size()
                + indexDirsManager.getAllLedgerDirs().size());
        allLedgerDirs.addAll(ledgerDirsManager.getAllLedgerDirs());
        if (indexDirsManager != ledgerDirsManager) {
            allLedgerDirs.addAll(indexDirsManager.getAllLedgerDirs());
        }
        // 校验目录结构和文件后缀
        if (metadataDriver == null) { // exists only for testing, just make sure directories are correct

            for (File journalDirectory : journalDirectories) {
                checkDirectoryStructure(journalDirectory);
            }

            for (File dir : allLedgerDirs) {
                checkDirectoryStructure(dir);
            }
            return;
        }

        // 校验配置的数据目录（journal和ledger）和实际磁盘中的目录是否有出入
        // 默认需要2者保持完全一致，通过配置allowStorageExpansion=true，允许配置中的目录比实际多（即扩容目录），但是不能比实际目录少(意味着可能丢数据)
        checkEnvironmentWithStorageExpansion(conf, metadataDriver, journalDirectories, allLedgerDirs);

        // 校验是否一个磁盘中有多个数据目录（默认允许这种行为）
        checkIfDirsOnSameDiskPartition(allLedgerDirs);
        checkIfDirsOnSameDiskPartition(journalDirectories);
    }

    /**
     * Checks if multiple directories are in same diskpartition/filesystem/device.
     * If ALLOW_MULTIPLEDIRS_UNDER_SAME_DISKPARTITION config parameter is not enabled, and
     * if it is found that there are multiple directories in the same DiskPartition then
     * it will throw DiskPartitionDuplicationException.
     *
     * @param dirs dirs to validate
     *
     * @throws IOException
     */
    private void checkIfDirsOnSameDiskPartition(List<File> dirs) throws DiskPartitionDuplicationException {
        // 是否允许一个盘有多个目录，默认true
        boolean allowDiskPartitionDuplication = conf.isAllowMultipleDirsUnderSameDiskPartition();
        final MutableBoolean isDuplicationFoundAndNotAllowed = new MutableBoolean(false);
        Map<FileStore, List<File>> fileStoreDirsMap = new HashMap<FileStore, List<File>>();
        for (File dir : dirs) {
            FileStore fileStore;
            try {
                fileStore = Files.getFileStore(dir.toPath());
            } catch (IOException e) {
                LOG.error("Got IOException while trying to FileStore of {}", dir);
                throw new BookieException.DiskPartitionDuplicationException(e);
            }
            if (fileStoreDirsMap.containsKey(fileStore)) {
                fileStoreDirsMap.get(fileStore).add(dir);
            } else {
                List<File> dirsList = new ArrayList<File>();
                dirsList.add(dir);
                fileStoreDirsMap.put(fileStore, dirsList);
            }
        }

        fileStoreDirsMap.forEach((fileStore, dirsList) -> {
            if (dirsList.size() > 1) {
                if (allowDiskPartitionDuplication) {
                    LOG.warn("Dirs: {} are in same DiskPartition/FileSystem: {}", dirsList, fileStore);
                } else {
                    LOG.error("Dirs: {} are in same DiskPartition/FileSystem: {}", dirsList, fileStore);
                    isDuplicationFoundAndNotAllowed.setValue(true);
                }
            }
        });
        if (isDuplicationFoundAndNotAllowed.getValue()) {
            throw new BookieException.DiskPartitionDuplicationException();
        }
    }

    static List<BookieId> possibleBookieIds(ServerConfiguration conf)
            throws BookieException {
        // we need to loop through all possible bookie identifiers to ensure it is treated as a new environment
        // just because of bad configuration
        List<BookieId> addresses = Lists.newArrayListWithExpectedSize(3);
        // we are checking all possibilities here, so we don't need to fail if we can only get
        // loopback address. it will fail anyway when the bookie attempts to listen on loopback address.
        try {
            // ip address
            addresses.add(getBookieAddress(
                new ServerConfiguration(conf)
                    .setUseHostNameAsBookieID(false)
                    .setAdvertisedAddress(null)
                    .setAllowLoopback(true)
            ).toBookieId());
            // host name
            addresses.add(getBookieAddress(
                new ServerConfiguration(conf)
                    .setUseHostNameAsBookieID(true)
                    .setAdvertisedAddress(null)
                    .setAllowLoopback(true)
            ).toBookieId());
            // advertised address
            if (null != conf.getAdvertisedAddress()) {
                addresses.add(getBookieAddress(conf).toBookieId());
            }
            if (null != conf.getBookieId()) {
                addresses.add(BookieId.parse(conf.getBookieId()));
            }
        } catch (UnknownHostException e) {
            throw new UnknownBookieIdException(e);
        }
        return addresses;
    }

    static Versioned<Cookie> readAndVerifyCookieFromRegistrationManager(
            Cookie masterCookie, RegistrationManager rm,
            List<BookieId> addresses, boolean allowExpansion)
            throws BookieException {
        Versioned<Cookie> rmCookie = null;
        for (BookieId address : addresses) {
            try {
                rmCookie = Cookie.readFromRegistrationManager(rm, address);
                // If allowStorageExpansion option is set, we should
                // make sure that the new set of ledger/index dirs
                // is a super set of the old; else, we fail the cookie check
                if (allowExpansion) {
                    masterCookie.verifyIsSuperSet(rmCookie.getValue());
                } else {
                    masterCookie.verify(rmCookie.getValue());
                }
            } catch (CookieNotFoundException e) {
                continue;
            }
        }
        return rmCookie;
    }

    private static Pair<List<File>, List<Cookie>> verifyAndGetMissingDirs(
            Cookie masterCookie, boolean allowExpansion, List<File> dirs)
            throws InvalidCookieException, IOException {
        List<File> missingDirs = Lists.newArrayList();
        List<Cookie> existedCookies = Lists.newArrayList();
        for (File dir : dirs) {
            checkDirectoryStructure(dir);
            try {
                Cookie c = Cookie.readFromDirectory(dir);
                if (allowExpansion) {
                    masterCookie.verifyIsSuperSet(c);
                } else {
                    masterCookie.verify(c);
                }
                existedCookies.add(c);
            } catch (FileNotFoundException fnf) {
                missingDirs.add(dir);
            }
        }
        return Pair.of(missingDirs, existedCookies);
    }

    private static void stampNewCookie(ServerConfiguration conf,
                                       Cookie masterCookie,
                                       RegistrationManager rm,
                                       Version version,
                                       List<File> journalDirectories,
                                       List<File> allLedgerDirs)
            throws BookieException, IOException {
        // backfill all the directories that miss cookies (for storage expansion)
        LOG.info("Stamping new cookies on all dirs {} {}",
                 journalDirectories, allLedgerDirs);
        for (File journalDirectory : journalDirectories) {
            masterCookie.writeToDirectory(journalDirectory);
        }
        for (File dir : allLedgerDirs) {
            masterCookie.writeToDirectory(dir);
        }
        masterCookie.writeToRegistrationManager(rm, conf, version);
    }

    public static void checkEnvironmentWithStorageExpansion(
            ServerConfiguration conf,
            MetadataBookieDriver metadataDriver,
            List<File> journalDirectories,
            List<File> allLedgerDirs) throws BookieException {
        RegistrationManager rm = metadataDriver.getRegistrationManager();
        try {
            // 1. retrieve the instance id
            String instanceId = rm.getClusterInstanceId();

            // 2. build the master cookie from the configuration
            Cookie.Builder builder = Cookie.generateCookie(conf);
            if (null != instanceId) {
                builder.setInstanceId(instanceId);
            }
            Cookie masterCookie = builder.build();
            boolean allowExpansion = conf.getAllowStorageExpansion();

            // 3. read the cookie from registration manager. it is the `source-of-truth` of a given bookie.
            //    if it doesn't exist in registration manager, this bookie is a new bookie, otherwise it is
            //    an old bookie.
            // 从注册中心读取当前bookie的信息(rmCookie)，读取不到说明当前是一个全选的bookie启动
            List<BookieId> possibleBookieIds = possibleBookieIds(conf);
            final Versioned<Cookie> rmCookie = readAndVerifyCookieFromRegistrationManager(
                        masterCookie, rm, possibleBookieIds, allowExpansion);

            // 4. check if the cookie appear in all the directories.
            List<File> missedCookieDirs = new ArrayList<>();
            List<Cookie> existingCookies = Lists.newArrayList();
            if (null != rmCookie) {
                existingCookies.add(rmCookie.getValue());
            }

            // 4.1 verify the cookies in journal directories
            // 校验当前配置的journalDirectories是否实际存在磁盘上
            Pair<List<File>, List<Cookie>> journalResult =
                verifyAndGetMissingDirs(masterCookie,
                                        allowExpansion, journalDirectories);
            missedCookieDirs.addAll(journalResult.getLeft());
            existingCookies.addAll(journalResult.getRight());
            // 4.2. verify the cookies in ledger directories
            // 校验当前配置的ledgerDirectories是否实际存在磁盘上
            Pair<List<File>, List<Cookie>> ledgerResult =
                verifyAndGetMissingDirs(masterCookie,
                                        allowExpansion, allLedgerDirs);
            missedCookieDirs.addAll(ledgerResult.getLeft());
            existingCookies.addAll(ledgerResult.getRight());

            // 5. if there are directories missing cookies,
            //    this is either a:
            //    - new environment
            //    - a directory is being added
            //    - a directory has been corrupted/wiped, which is an error
            // 如果有存在配置不存在目录（配置存在目录，但是实际没有），则存在以下3中情况：
            //    - 这是一个全新启动的bookie
            //    - 新增加了一个目录（allowStorageExpansion必须设置为true）
            //    - 某个目录顺换或者目录中的数据被擦除(一种异常情况)
            if (!missedCookieDirs.isEmpty()) {
                if (rmCookie == null) {
                    // 5.1 new environment: all directories should be empty
                    verifyDirsForNewEnvironment(missedCookieDirs);
                    stampNewCookie(conf, masterCookie, rm, Version.NEW,
                                   journalDirectories, allLedgerDirs);
                } else if (allowExpansion) {
                    // 5.2 storage is expanding
                    Set<File> knownDirs = getKnownDirs(existingCookies);
                    verifyDirsForStorageExpansion(missedCookieDirs, knownDirs);
                    stampNewCookie(conf, masterCookie,
                                   rm, rmCookie.getVersion(),
                                   journalDirectories, allLedgerDirs);
                } else {
                    // 5.3 Cookie-less directories and
                    //     we can't do anything with them
                    LOG.error("There are directories without a cookie,"
                              + " and this is neither a new environment,"
                              + " nor is storage expansion enabled. "
                              + "Empty directories are {}", missedCookieDirs);
                    throw new InvalidCookieException();
                }
            } else {
                if (rmCookie == null) {
                    // No corresponding cookie found in registration manager. The bookie should fail to come up.
                    LOG.error("Cookie for this bookie is not stored in metadata store. Bookie failing to come up");
                    throw new InvalidCookieException();
                }
            }
        } catch (IOException ioe) {
            LOG.error("Error accessing cookie on disks", ioe);
            throw new BookieException.InvalidCookieException(ioe);
        }
    }

    private static void verifyDirsForNewEnvironment(List<File> missedCookieDirs)
            throws InvalidCookieException {
        List<File> nonEmptyDirs = new ArrayList<>();
        for (File dir : missedCookieDirs) {
            String[] content = dir.list();
            if (content != null && content.length != 0) {
                nonEmptyDirs.add(dir);
            }
        }
        if (!nonEmptyDirs.isEmpty()) {
            LOG.error("Not all the new directories are empty. New directories that are not empty are: " + nonEmptyDirs);
            throw new InvalidCookieException();
        }
    }

    private static Set<File> getKnownDirs(List<Cookie> cookies) {
        return cookies.stream()
            .flatMap((c) -> Arrays.stream(c.getLedgerDirPathsFromCookie()))
            .map((s) -> new File(s))
            .collect(Collectors.toSet());
    }

    private static void verifyDirsForStorageExpansion(
            List<File> missedCookieDirs,
            Set<File> existingLedgerDirs) throws InvalidCookieException {

        List<File> dirsMissingData = new ArrayList<File>();
        List<File> nonEmptyDirs = new ArrayList<File>();
        for (File dir : missedCookieDirs) {
            if (existingLedgerDirs.contains(dir.getParentFile())) {
                // if one of the existing ledger dirs doesn't have cookie,
                // let us not proceed further
                dirsMissingData.add(dir);
                continue;
            }
            String[] content = dir.list();
            if (content != null && content.length != 0) {
                nonEmptyDirs.add(dir);
            }
        }
        if (dirsMissingData.size() > 0 || nonEmptyDirs.size() > 0) {
            LOG.error("Either not all local directories have cookies or directories being added "
                    + " newly are not empty. "
                    + "Directories missing cookie file are: " + dirsMissingData
                    + " New directories that are not empty are: " + nonEmptyDirs);
            throw new InvalidCookieException();
        }
    }

    public static BookieId getBookieId(ServerConfiguration conf) throws UnknownHostException {
        String customBookieId = conf.getBookieId();
        if (customBookieId != null) {
            return BookieId.parse(customBookieId);
        }
        return getBookieAddress(conf).toBookieId();
    }

    /**
     * Return the configured address of the bookie.
     */
    public static BookieSocketAddress getBookieAddress(ServerConfiguration conf)
            throws UnknownHostException {
        // Advertised address takes precedence over the listening interface and the
        // useHostNameAsBookieID settings
        if (conf.getAdvertisedAddress() != null && conf.getAdvertisedAddress().trim().length() > 0) {
            String hostAddress = conf.getAdvertisedAddress().trim();
            return new BookieSocketAddress(hostAddress, conf.getBookiePort());
        }

        String iface = conf.getListeningInterface();
        if (iface == null) {
            iface = "default";
        }

        String hostName = DNS.getDefaultHost(iface);
        InetSocketAddress inetAddr = new InetSocketAddress(hostName, conf.getBookiePort());
        if (inetAddr.isUnresolved()) {
            throw new UnknownHostException("Unable to resolve default hostname: "
                    + hostName + " for interface: " + iface);
        }
        String hostAddress = null;
        InetAddress iAddress = inetAddr.getAddress();
        if (conf.getUseHostNameAsBookieID()) {
            hostAddress = iAddress.getCanonicalHostName();
            if (conf.getUseShortHostName()) {
                /*
                 * if short hostname is used, then FQDN is not used. Short
                 * hostname is the hostname cut at the first dot.
                 */
                hostAddress = hostAddress.split("\\.", 2)[0];
            }
        } else {
            hostAddress = iAddress.getHostAddress();
        }

        BookieSocketAddress addr =
                new BookieSocketAddress(hostAddress, conf.getBookiePort());
        if (addr.getSocketAddress().getAddress().isLoopbackAddress()
            && !conf.getAllowLoopback()) {
            throw new UnknownHostException("Trying to listen on loopback address, "
                    + addr + " but this is forbidden by default "
                    + "(see ServerConfiguration#getAllowLoopback()).\n"
                    + "If this happen, you can consider specifying the network interface"
                    + " to listen on (e.g. listeningInterface=eth0) or specifying the"
                    + " advertised address (e.g. advertisedAddress=172.x.y.z)");
        }
        return addr;
    }

    public LedgerDirsManager getLedgerDirsManager() {
        return ledgerDirsManager;
    }

    LedgerDirsManager getIndexDirsManager() {
        return indexDirsManager;
    }

    public long getTotalDiskSpace() throws IOException {
        return getLedgerDirsManager().getTotalDiskSpace(ledgerDirsManager.getAllLedgerDirs());
    }

    public long getTotalFreeSpace() throws IOException {
        return getLedgerDirsManager().getTotalFreeSpace(ledgerDirsManager.getAllLedgerDirs());
    }

    public static File getCurrentDirectory(File dir) {
        return new File(dir, BookKeeperConstants.CURRENT_DIR);
    }

    public static File[] getCurrentDirectories(File[] dirs) {
        File[] currentDirs = new File[dirs.length];
        for (int i = 0; i < dirs.length; i++) {
            currentDirs[i] = getCurrentDirectory(dirs[i]);
        }
        return currentDirs;
    }

    public BookieImpl(ServerConfiguration conf)
            throws IOException, InterruptedException, BookieException {
        this(conf, NullStatsLogger.INSTANCE, PooledByteBufAllocator.DEFAULT, new SimpleBookieServiceInfoProvider(conf));
    }

    private static LedgerStorage buildLedgerStorage(ServerConfiguration conf) throws IOException {
        // Instantiate the ledger storage implementation
        String ledgerStorageClass = conf.getLedgerStorageClass();
        LOG.info("Using ledger storage: {}", ledgerStorageClass);
        return LedgerStorageFactory.createLedgerStorage(ledgerStorageClass);
    }

    /**
     * Initialize LedgerStorage instance without checkpointing for use within the shell
     * and other RO users.  ledgerStorage must not have already been initialized.
     *
     * <p>The caller is responsible for disposing of the ledgerStorage object.
     *
     * @param conf Bookie config.
     * @param ledgerStorage Instance to initialize.
     * @return Passed ledgerStorage instance
     * @throws IOException
     */
    public static LedgerStorage mountLedgerStorageOffline(ServerConfiguration conf, LedgerStorage ledgerStorage)
            throws IOException {
        StatsLogger statsLogger = NullStatsLogger.INSTANCE;
        DiskChecker diskChecker = new DiskChecker(conf.getDiskUsageThreshold(), conf.getDiskUsageWarnThreshold());

        LedgerDirsManager ledgerDirsManager = createLedgerDirsManager(
                conf, diskChecker, statsLogger.scope(LD_LEDGER_SCOPE));
        LedgerDirsManager indexDirsManager = createIndexDirsManager(
                conf, diskChecker, statsLogger.scope(LD_INDEX_SCOPE), ledgerDirsManager);

        if (null == ledgerStorage) {
            ledgerStorage = buildLedgerStorage(conf);
        }

        CheckpointSource checkpointSource = new CheckpointSource() {
            @Override
            public Checkpoint newCheckpoint() {
                return Checkpoint.MAX;
            }

            @Override
            public void checkpointComplete(Checkpoint checkpoint, boolean compact)
                    throws IOException {
            }
        };

        Checkpointer checkpointer = Checkpointer.NULL;

        ledgerStorage.initialize(
                conf,
                null,
                ledgerDirsManager,
                indexDirsManager,
                null,
                checkpointSource,
                checkpointer,
                statsLogger,
                UnpooledByteBufAllocator.DEFAULT);

        return ledgerStorage;
    }

    public BookieImpl(ServerConfiguration conf, StatsLogger statsLogger,
                      ByteBufAllocator allocator, Supplier<BookieServiceInfo> bookieServiceInfoProvider)
            throws IOException, InterruptedException, BookieException {
        super("Bookie-" + conf.getBookiePort());
        this.bookieServiceInfoProvider = bookieServiceInfoProvider;
        this.statsLogger = statsLogger;
        this.conf = conf;
        this.journalDirectories = Lists.newArrayList();
        // 1. 获取配置的journal目录，并在每个journal目录下创建current目录
        for (File journalDirectory : conf.getJournalDirs()) {
            this.journalDirectories.add(getCurrentDirectory(journalDirectory));
        }
        // 2. 创建磁盘检查：检查每个配置的目录使用量。2个参数：
        //  * diskUsageThreshold: 默认每个目录最大可以使用磁盘95%的空间。如果所有的ledger目录都超过阈值，bookie将进入只读状态
        //  * diskUsageWarnThreshold: 磁盘可用空间下限阈值，默认磁盘90%的空间。如果超过这个阈值，将会认为磁盘已满，并触发gc(非jvm gc)来清理数据。
        //      当发生并发写和数据压缩的时候，这也可以防止bookie频繁在只读和读写状态来回切换
        DiskChecker diskChecker = createDiskChecker(conf);
        // 3. 创建ledger目录管理
        this.ledgerDirsManager = createLedgerDirsManager(conf, diskChecker, statsLogger.scope(LD_LEDGER_SCOPE));
        // 4. 创建index目录管理：index目录中是ledger的索引文件，由于ledger目录中所有ledger数据都写在同一个文件中，因此需要索引文件来标识每个ledger数据的offset
        //      默认直接使用ledger目录
        this.indexDirsManager = createIndexDirsManager(conf, diskChecker, statsLogger.scope(LD_INDEX_SCOPE),
                                                       this.ledgerDirsManager);
        this.writeDataToJournal = conf.getJournalWriteData();
        this.allocator = allocator;

        // instantiate zookeeper client to initialize ledger manager
        // 5. 实例化zk driver，用来操作zk上的bookie元数据
        this.metadataDriver = instantiateMetadataDriver(conf);
        // 6. 校验环境，主要是配置的数据目录（journal和ledger目录）和磁盘实际存在的目录比较
        checkEnvironment(this.metadataDriver);
        try {
            if (this.metadataDriver != null) {
                // current the registration manager is zookeeper only
                // 默认为HierarchicalLedgerManagerFactory
                ledgerManagerFactory = metadataDriver.getLedgerManagerFactory();
                LOG.info("instantiate ledger manager {}", ledgerManagerFactory.getClass().getName());
                // 默认为HierarchicalLedgerManager
                ledgerManager = ledgerManagerFactory.newLedgerManager();
            } else {
                ledgerManagerFactory = null;
                ledgerManager = null;
            }
        } catch (MetadataException e) {
            throw new MetadataStoreException("Failed to initialize ledger manager", e);
        }
        stateManager = initializeStateManager();
        // register shutdown handler using trigger mode
        stateManager.setShutdownHandler(exitCode -> triggerBookieShutdown(exitCode));
        // Initialise dirsMonitor. This would look through all the
        // configured directories. When disk errors or all the ledger
        // directories are full, would throws exception and fail bookie startup.
        // 7. 多个ledger目录的监控包装为dirsMonitor
        List<LedgerDirsManager> dirsManagers = new ArrayList<>();
        dirsManagers.add(ledgerDirsManager);
        if (indexDirsManager != ledgerDirsManager) {
            dirsManagers.add(indexDirsManager);
        }
        this.dirsMonitor = new LedgerDirsMonitor(conf, diskChecker, dirsManagers);
        try {
            this.dirsMonitor.init();
        } catch (NoWritableLedgerDirException nle) {
            // start in read-only mode if no writable dirs and read-only allowed
            if (!conf.isReadOnlyModeEnabled()) {
                throw nle;
            } else {
                this.stateManager.transitionToReadOnlyMode();
            }
        }

        // instantiate the journals
        // 8. 实例化journals
        journals = Lists.newArrayList();
        for (int i = 0; i < journalDirectories.size(); i++) {
            journals.add(new Journal(i, journalDirectories.get(i),
                    conf, ledgerDirsManager, statsLogger.scope(JOURNAL_SCOPE), allocator));
        }

        this.entryLogPerLedgerEnabled = conf.isEntryLogPerLedgerEnabled();
        CheckpointSource checkpointSource = new CheckpointSourceList(journals);

        // 9. 创建ledgerStorage, 默认为SortedLedgerStorage
        ledgerStorage = buildLedgerStorage(conf);

        // 默认false
        boolean isDbLedgerStorage = ledgerStorage instanceof DbLedgerStorage;

        /*
         * with this change https://github.com/apache/bookkeeper/pull/677,
         * LedgerStorage drives the checkpoint logic.
         *
         * <p>There are two exceptions:
         *
         * 1) with multiple entry logs, checkpoint logic based on a entry log is
         *    not possible, hence it needs to be timebased recurring thing and
         *    it is driven by SyncThread. SyncThread.start does that and it is
         *    started in Bookie.start method.
         *
         * 2) DbLedgerStorage
         */
        // LedgerStorage驱动执行checkpoint逻辑，但是有2个例外情况：
        // 1. entryLogPerLedgerEnabled=true的情况下，有多个entry log，原先基于单个entry log的checkpoint逻辑不适用。因此需要定时的去做checkpoint
        // 2. DbLedgerStorage
        if (entryLogPerLedgerEnabled || isDbLedgerStorage) {
            syncThread = new SyncThread(conf, getLedgerDirsListener(), ledgerStorage, checkpointSource) {
                @Override
                public void startCheckpoint(Checkpoint checkpoint) {
                    /*
                     * in the case of entryLogPerLedgerEnabled, LedgerStorage
                     * dont drive checkpoint logic, but instead it is done
                     * periodically by SyncThread. So startCheckpoint which
                     * will be called by LedgerStorage will be no-op.
                     */
                }

                @Override
                public void start() {
                    executor.scheduleAtFixedRate(() -> {
                        doCheckpoint(checkpointSource.newCheckpoint());
                    }, conf.getFlushInterval(), conf.getFlushInterval(), TimeUnit.MILLISECONDS);
                }
            };
        } else {
            // syncThread用来组织ledgerStorage和journal文件:
            // 1. 当ledgerStorage.checkpoint()完成后，journal可以安全的删除检查点之前的数据
            // 2. 装饰ledgerStorage.flush()
            syncThread = new SyncThread(conf, getLedgerDirsListener(), ledgerStorage, checkpointSource);
        }

        // 初始化ledgerStorage
        ledgerStorage.initialize(
            conf,
            ledgerManager,
            ledgerDirsManager,
            indexDirsManager,
            stateManager,
            checkpointSource,
            syncThread,
            statsLogger,
            allocator);


        // handle工厂，这个handle是LedgerDescriptorImpl，包装了ledgerStorage，用来读写某个ledgerId对应的ledger的entry
        handles = new HandleFactoryImpl(ledgerStorage);

        // Expose Stats
        // 暴露一些统计指标
        this.bookieStats = new BookieStats(statsLogger);
        journalMemoryMaxStats = new Gauge<Long>() {
            final long journalMaxMemory = conf.getJournalMaxMemorySizeMb() * 1024 * 1024;

            @Override
            public Long getDefaultValue() {
                return journalMaxMemory;
            }

            @Override
            public Long getSample() {
                return journalMaxMemory;
            }
        };
        statsLogger.scope(JOURNAL_SCOPE).registerGauge(JOURNAL_MEMORY_MAX, journalMemoryMaxStats);

        journalMemoryUsedStats = new Gauge<Long>() {
            @Override
            public Long getDefaultValue() {
                return -1L;
            }

            @Override
            public Long getSample() {
                long totalMemory = 0L;
                for (int i = 0; i < journals.size(); i++) {
                    totalMemory += journals.get(i).getMemoryUsage();
                }
                return totalMemory;
            }
        };
        statsLogger.scope(JOURNAL_SCOPE).registerGauge(JOURNAL_MEMORY_USED, journalMemoryUsedStats);
    }

    StateManager initializeStateManager() throws IOException {
        return new BookieStateManager(conf, statsLogger, metadataDriver,
                ledgerDirsManager, bookieServiceInfoProvider);
    }

    void readJournal() throws IOException, BookieException {
        long startTs = System.currentTimeMillis();
        JournalScanner scanner = new JournalScanner() {
            @Override
            public void process(int journalVersion, long offset, ByteBuffer recBuff) throws IOException {
                long ledgerId = recBuff.getLong();
                long entryId = recBuff.getLong();
                try {
                    if (LOG.isDebugEnabled()) {
                        LOG.debug("Replay journal - ledger id : {}, entry id : {}.", ledgerId, entryId);
                    }
                    if (entryId == METAENTRY_ID_LEDGER_KEY) {
                        if (journalVersion >= JournalChannel.V3) {
                            int masterKeyLen = recBuff.getInt();
                            byte[] masterKey = new byte[masterKeyLen];

                            recBuff.get(masterKey);
                            masterKeyCache.put(ledgerId, masterKey);

                            // Force to re-insert the master key in ledger storage
                            handles.getHandle(ledgerId, masterKey);
                        } else {
                            throw new IOException("Invalid journal. Contains journalKey "
                                    + " but layout version (" + journalVersion
                                    + ") is too old to hold this");
                        }
                    } else if (entryId == METAENTRY_ID_FENCE_KEY) {
                        if (journalVersion >= JournalChannel.V4) {
                            byte[] key = masterKeyCache.get(ledgerId);
                            if (key == null) {
                                key = ledgerStorage.readMasterKey(ledgerId);
                            }
                            LedgerDescriptor handle = handles.getHandle(ledgerId, key);
                            handle.setFenced();
                        } else {
                            throw new IOException("Invalid journal. Contains fenceKey "
                                    + " but layout version (" + journalVersion
                                    + ") is too old to hold this");
                        }
                    } else if (entryId == METAENTRY_ID_LEDGER_EXPLICITLAC) {
                        if (journalVersion >= JournalChannel.V6) {
                            int explicitLacBufLength = recBuff.getInt();
                            ByteBuf explicitLacBuf = Unpooled.buffer(explicitLacBufLength);
                            byte[] explicitLacBufArray = new byte[explicitLacBufLength];
                            recBuff.get(explicitLacBufArray);
                            explicitLacBuf.writeBytes(explicitLacBufArray);
                            byte[] key = masterKeyCache.get(ledgerId);
                            if (key == null) {
                                key = ledgerStorage.readMasterKey(ledgerId);
                            }
                            LedgerDescriptor handle = handles.getHandle(ledgerId, key);
                            handle.setExplicitLac(explicitLacBuf);
                        } else {
                            throw new IOException("Invalid journal. Contains explicitLAC " + " but layout version ("
                                    + journalVersion + ") is too old to hold this");
                        }
                    } else if (entryId < 0) {
                        /*
                         * this is possible if bookie code binary is rolledback
                         * to older version but when it is trying to read
                         * Journal which was created previously using newer
                         * code/journalversion, which introduced new special
                         * entry. So in anycase, if we see unrecognizable
                         * special entry while replaying journal we should skip
                         * (ignore) it.
                         */
                        LOG.warn("Read unrecognizable entryId: {} for ledger: {} while replaying Journal. Skipping it",
                                entryId, ledgerId);
                    } else {
                        byte[] key = masterKeyCache.get(ledgerId);
                        if (key == null) {
                            key = ledgerStorage.readMasterKey(ledgerId);
                        }
                        LedgerDescriptor handle = handles.getHandle(ledgerId, key);

                        recBuff.rewind();
                        handle.addEntry(Unpooled.wrappedBuffer(recBuff));
                    }
                } catch (NoLedgerException nsle) {
                    if (LOG.isDebugEnabled()) {
                        LOG.debug("Skip replaying entries of ledger {} since it was deleted.", ledgerId);
                    }
                } catch (BookieException be) {
                    throw new IOException(be);
                }
            }
        };

        for (Journal journal : journals) {
            replay(journal, scanner);
        }
        long elapsedTs = System.currentTimeMillis() - startTs;
        LOG.info("Finished replaying journal in {} ms.", elapsedTs);
    }

    /**
     * Replay journal files and updates journal's in-memory lastLogMark object.
     *
     * @param journal Journal object corresponding to a journalDir
     * @param scanner Scanner to process replayed entries.
     * @throws IOException
     */
    private void replay(Journal journal, JournalScanner scanner) throws IOException {
        final LogMark markedLog = journal.getLastLogMark().getCurMark();
        List<Long> logs = Journal.listJournalIds(journal.getJournalDirectory(), journalId ->
            journalId >= markedLog.getLogFileId());
        // last log mark may be missed due to no sync up before
        // validate filtered log ids only when we have markedLogId
        if (markedLog.getLogFileId() > 0) {
            if (logs.size() == 0 || logs.get(0) != markedLog.getLogFileId()) {
                throw new IOException("Recovery log " + markedLog.getLogFileId() + " is missing");
            }
        }

        // TODO: When reading in the journal logs that need to be synced, we
        // should use BufferedChannels instead to minimize the amount of
        // system calls done.
        for (Long id : logs) {
            long logPosition = 0L;
            if (id == markedLog.getLogFileId()) {
                logPosition = markedLog.getLogFileOffset();
            }
            LOG.info("Replaying journal {} from position {}", id, logPosition);
            long scanOffset = journal.scanJournal(id, logPosition, scanner);
            // Update LastLogMark after completely replaying journal
            // scanOffset will point to EOF position
            // After LedgerStorage flush, SyncThread should persist this to disk
            journal.setLastLogMark(id, scanOffset);
        }
    }

    @Override
    public synchronized void start() {
        // 设置为守护线程
        setDaemon(true);
        if (LOG.isDebugEnabled()) {
            LOG.debug("I'm starting a bookie with journal directories {}",
                    journalDirectories.stream().map(File::getName).collect(Collectors.joining(", ")));
        }
        //Start DiskChecker thread
        // 1. 启动磁盘监控线程
        dirsMonitor.start();

        // replay journals
        // 2. 重放journal.可能这次启动是由于异常情况而重启，journal的数据还未整理刷到ledger
        try {
            readJournal();
        } catch (IOException | BookieException ioe) {
            LOG.error("Exception while replaying journals, shutting down", ioe);
            shutdown(ExitCode.BOOKIE_EXCEPTION);
            return;
        }

        // Do a fully flush after journal replay
        // 3. journal重放后，将数据刷盘到ledger,并且会删除journal中已经刷盘的wal日志
        try {
            syncThread.requestFlush().get();
        } catch (InterruptedException e) {
            LOG.warn("Interrupting the fully flush after replaying journals : ", e);
            Thread.currentThread().interrupt();
        } catch (ExecutionException e) {
            LOG.error("Error on executing a fully flush after replaying journals.");
            shutdown(ExitCode.BOOKIE_EXCEPTION);
            return;
        }

        // 4. 是否在启动的时候进行一次本地数据一致性检查，默认false.
        if (conf.isLocalConsistencyCheckOnStartup()) {
            LOG.info("Running local consistency check on startup prior to accepting IO.");
            List<LedgerStorage.DetectedInconsistency> errors = null;
            try {
                // 最终调用的是InterleavedLedgerStorage.localConsistencyCheck(),(和创建bookie服务阶段创建的ScrubberService做的是同一件事)
                // 仅仅检查写入到EntryLog文件中的entry字节中的元数据（ledgerId、entryId）是否和IndexCache中记录的一致
                errors = ledgerStorage.localConsistencyCheck(Optional.empty());
            } catch (IOException e) {
                LOG.error("Got a fatal exception while checking store", e);
                shutdown(ExitCode.BOOKIE_EXCEPTION);
                return;
            }
            if (errors != null && errors.size() > 0) {
                LOG.error("Bookie failed local consistency check:");
                for (LedgerStorage.DetectedInconsistency error : errors) {
                    LOG.error("Ledger {}, entry {}: ", error.getLedgerId(), error.getEntryId(), error.getException());
                }
                shutdown(ExitCode.BOOKIE_EXCEPTION);
                return;
            }
        }

        LOG.info("Finished reading journal, starting bookie");


        /*
         * start sync thread first, so during replaying journals, we could do
         * checkpoint which reduce the chance that we need to replay journals
         * again if bookie restarted again before finished journal replays.
         */
        // 默认空方法，只有在启用多entry log的时候才会启动一个定时checkpoint的任务(详见BookieImpl#795)
        syncThread.start();

        // start bookie thread
        // 5. 启动bookie线程
        super.start();

        // After successful bookie startup, register listener for disk
        // error/full notifications.
        ledgerDirsManager.addLedgerDirsListener(getLedgerDirsListener());
        if (indexDirsManager != ledgerDirsManager) {
            indexDirsManager.addLedgerDirsListener(getLedgerDirsListener());
        }

        // 6. 启动ledger存储管理
        ledgerStorage.start();

        // check the bookie status to start with, and set running.
        // since bookie server use running as a flag to tell bookie server whether it is alive
        // if setting it in bookie thread, the watcher might run before bookie thread.
        stateManager.initState();

        // 7. 将bookie的相关元数据注册到zk以供集群发现
        try {
            stateManager.registerBookie(true).get();
        } catch (Exception e) {
            LOG.error("Couldn't register bookie with zookeeper, shutting down : ", e);
            shutdown(ExitCode.ZK_REG_FAIL);
        }
    }

    /*
     * Get the DiskFailure listener for the bookie
     */
    private LedgerDirsListener getLedgerDirsListener() {

        return new LedgerDirsListener() {

            @Override
            public void diskFailed(File disk) {
                // Shutdown the bookie on disk failure.
                triggerBookieShutdown(ExitCode.BOOKIE_EXCEPTION);
            }

            @Override
            public void allDisksFull(boolean highPriorityWritesAllowed) {
                // Transition to readOnly mode on all disks full
                stateManager.setHighPriorityWritesAvailability(highPriorityWritesAllowed);
                stateManager.transitionToReadOnlyMode();
            }

            @Override
            public void fatalError() {
                LOG.error("Fatal error reported by ledgerDirsManager");
                triggerBookieShutdown(ExitCode.BOOKIE_EXCEPTION);
            }

            @Override
            public void diskWritable(File disk) {
                // Transition to writable mode when a disk becomes writable again.
                stateManager.setHighPriorityWritesAvailability(true);
                stateManager.transitionToWritableMode();
            }

            @Override
            public void diskJustWritable(File disk) {
                // Transition to writable mode when a disk becomes writable again.
                stateManager.setHighPriorityWritesAvailability(true);
                stateManager.transitionToWritableMode();
            }
        };
    }

    /**
     * Instantiate the metadata driver for the Bookie.
     */
    private MetadataBookieDriver instantiateMetadataDriver(ServerConfiguration conf) throws BookieException {
        try {
            String metadataServiceUriStr = conf.getMetadataServiceUri();
            if (null == metadataServiceUriStr) {
                return null;
            }

            MetadataBookieDriver driver = MetadataDrivers.getBookieDriver(
                URI.create(metadataServiceUriStr));
            driver.initialize(
                conf,
                () -> {
                    stateManager.forceToUnregistered();
                    // schedule a re-register operation
                    stateManager.registerBookie(false);
                },
                statsLogger);
            return driver;
        } catch (MetadataException me) {
            throw new MetadataStoreException("Failed to initialize metadata bookie driver", me);
        } catch (ConfigurationException e) {
            throw new BookieIllegalOpException(e);
        }
    }

    /*
     * Check whether Bookie is writable.
     */
    public boolean isReadOnly() {
        return stateManager.isReadOnly();
    }

    /**
     * Check whether Bookie is available for high priority writes.
     *
     * @return true if the bookie is able to take high priority writes.
     */
    public boolean isAvailableForHighPriorityWrites() {
        return stateManager.isAvailableForHighPriorityWrites();
    }

    public boolean isRunning() {
        return stateManager.isRunning();
    }

    @Override
    public void run() {
        // bookie thread wait for journal thread
        try {
            // start journals
            for (Journal journal: journals) {
                journal.start();
            }

            // wait until journal quits
            for (Journal journal: journals) {

                journal.joinThread();
            }
            LOG.info("Journal thread(s) quit.");
        } catch (InterruptedException ie) {
            Thread.currentThread().interrupt();
            LOG.warn("Interrupted on running journal thread : ", ie);
        }
        // if the journal thread quits due to shutting down, it is ok
        if (!stateManager.isShuttingDown()) {
            // some error found in journal thread and it quits
            // following add operations to it would hang unit client timeout
            // so we should let bookie server exists
            LOG.error("Journal manager quits unexpectedly.");
            triggerBookieShutdown(ExitCode.BOOKIE_EXCEPTION);
        }
    }

    // Triggering the Bookie shutdown in its own thread,
    // because shutdown can be called from sync thread which would be
    // interrupted by shutdown call.
    AtomicBoolean shutdownTriggered = new AtomicBoolean(false);
    void triggerBookieShutdown(final int exitCode) {
        if (!shutdownTriggered.compareAndSet(false, true)) {
            return;
        }
        LOG.info("Triggering shutdown of Bookie-{} with exitCode {}",
                 conf.getBookiePort(), exitCode);
        BookieThread th = new BookieThread("BookieShutdownTrigger") {
            @Override
            public void run() {
                BookieImpl.this.shutdown(exitCode);
            }
        };
        th.start();
    }

    // provided a public shutdown method for other caller
    // to shut down bookie gracefully
    public int shutdown() {
        return shutdown(ExitCode.OK);
    }

    // internal shutdown method to let shutdown bookie gracefully
    // when encountering exception
    synchronized int shutdown(int exitCode) {
        try {
            if (isRunning()) { // avoid shutdown twice
                // the exitCode only set when first shutdown usually due to exception found
                LOG.info("Shutting down Bookie-{} with exitCode {}",
                         conf.getBookiePort(), exitCode);
                if (this.exitCode == ExitCode.OK) {
                    this.exitCode = exitCode;
                }

                stateManager.forceToShuttingDown();

                // turn bookie to read only during shutting down process
                LOG.info("Turning bookie to read only during shut down");
                stateManager.forceToReadOnly();

                // Shutdown Sync thread
                syncThread.shutdown();

                // Shutdown journals
                for (Journal journal : journals) {
                    journal.shutdown();
                }
                this.join();

                // Shutdown the EntryLogger which has the GarbageCollector Thread running
                ledgerStorage.shutdown();

                // close Ledger Manager
                try {
                    if (null != ledgerManager) {
                        ledgerManager.close();
                    }
                    if (null != ledgerManagerFactory) {
                        ledgerManagerFactory.close();
                    }
                } catch (IOException ie) {
                    LOG.error("Failed to close active ledger manager : ", ie);
                }

                //Shutdown disk checker
                dirsMonitor.shutdown();
            }
            // Shutdown the ZK client
            if (metadataDriver != null) {
                metadataDriver.close();
            }
        } catch (InterruptedException ie) {
            Thread.currentThread().interrupt();
            LOG.error("Interrupted during shutting down bookie : ", ie);
        } catch (Exception e) {
            LOG.error("Got Exception while trying to shutdown Bookie", e);
            throw e;
        } finally {
            // setting running to false here, so watch thread
            // in bookie server know it only after bookie shut down
            stateManager.close();
        }
        return this.exitCode;
    }

    /**
     * Retrieve the ledger descriptor for the ledger which entry should be added to.
     * The LedgerDescriptor returned from this method should be eventually freed with
     * #putHandle().
     *
     * @throws BookieException if masterKey does not match the master key of the ledger
     */
    @VisibleForTesting
    LedgerDescriptor getLedgerForEntry(ByteBuf entry, final byte[] masterKey)
            throws IOException, BookieException {
        final long ledgerId = entry.getLong(entry.readerIndex());

        return handles.getHandle(ledgerId, masterKey);
    }

    private Journal getJournal(long ledgerId) {
        return journals.get(MathUtils.signSafeMod(ledgerId, journals.size()));
    }

    /**
     * Add an entry to a ledger as specified by handle.
     */
    private void addEntryInternal(LedgerDescriptor handle, ByteBuf entry,
                                  boolean ackBeforeSync, WriteCallback cb, Object ctx, byte[] masterKey)
            throws IOException, BookieException, InterruptedException {
        long ledgerId = handle.getLedgerId();
        long entryId = handle.addEntry(entry);

        bookieStats.getWriteBytes().add(entry.readableBytes());

        // journal `addEntry` should happen after the entry is added to ledger storage.
        // otherwise the journal entry can potentially be rolled before the ledger is created in ledger storage.
        if (masterKeyCache.get(ledgerId) == null) {
            // Force the load into masterKey cache
            byte[] oldValue = masterKeyCache.putIfAbsent(ledgerId, masterKey);
            if (oldValue == null) {
                // new handle, we should add the key to journal ensure we can rebuild
                ByteBuffer bb = ByteBuffer.allocate(8 + 8 + 4 + masterKey.length);
                bb.putLong(ledgerId);
                bb.putLong(METAENTRY_ID_LEDGER_KEY);
                bb.putInt(masterKey.length);
                bb.put(masterKey);
                bb.flip();

                getJournal(ledgerId).logAddEntry(bb, false /* ackBeforeSync */, new NopWriteCallback(), null);
            }
        }

        if (!writeDataToJournal) {
            cb.writeComplete(0, ledgerId, entryId, null, ctx);
            return;
        }

        if (LOG.isTraceEnabled()) {
            LOG.trace("Adding {}@{}", entryId, ledgerId);
        }
        getJournal(ledgerId).logAddEntry(entry, ackBeforeSync, cb, ctx);
    }

    /**
     * Add entry to a ledger, even if the ledger has previous been fenced. This should only
     * happen in bookie recovery or ledger recovery cases, where entries are being replicates
     * so that they exist on a quorum of bookies. The corresponding client side call for this
     * is not exposed to users.
     */
    public void recoveryAddEntry(ByteBuf entry, WriteCallback cb, Object ctx, byte[] masterKey)
            throws IOException, BookieException, InterruptedException {
        long requestNanos = MathUtils.nowInNano();
        boolean success = false;
        int entrySize = 0;
        try {
            LedgerDescriptor handle = getLedgerForEntry(entry, masterKey);
            synchronized (handle) {
                entrySize = entry.readableBytes();
                addEntryInternal(handle, entry, false /* ackBeforeSync */, cb, ctx, masterKey);
            }
            success = true;
        } catch (NoWritableLedgerDirException e) {
            stateManager.transitionToReadOnlyMode();
            throw new IOException(e);
        } finally {
            long elapsedNanos = MathUtils.elapsedNanos(requestNanos);
            if (success) {
                bookieStats.getRecoveryAddEntryStats().registerSuccessfulEvent(elapsedNanos, TimeUnit.NANOSECONDS);
                bookieStats.getAddBytesStats().registerSuccessfulValue(entrySize);
            } else {
                bookieStats.getRecoveryAddEntryStats().registerFailedEvent(elapsedNanos, TimeUnit.NANOSECONDS);
                bookieStats.getAddBytesStats().registerFailedValue(entrySize);
            }

            entry.release();
        }
    }

    private ByteBuf createExplicitLACEntry(long ledgerId, ByteBuf explicitLac) {
        ByteBuf bb = allocator.directBuffer(8 + 8 + 4 + explicitLac.capacity());
        bb.writeLong(ledgerId);
        bb.writeLong(METAENTRY_ID_LEDGER_EXPLICITLAC);
        bb.writeInt(explicitLac.capacity());
        bb.writeBytes(explicitLac);
        return bb;
    }

    public void setExplicitLac(ByteBuf entry, WriteCallback writeCallback, Object ctx, byte[] masterKey)
            throws IOException, InterruptedException, BookieException {
        try {
            long ledgerId = entry.getLong(entry.readerIndex());
            LedgerDescriptor handle = handles.getHandle(ledgerId, masterKey);
            synchronized (handle) {
                entry.markReaderIndex();
                handle.setExplicitLac(entry);
                entry.resetReaderIndex();
                ByteBuf explicitLACEntry = createExplicitLACEntry(ledgerId, entry);
                getJournal(ledgerId).logAddEntry(explicitLACEntry, false /* ackBeforeSync */, writeCallback, ctx);
            }
        } catch (NoWritableLedgerDirException e) {
            stateManager.transitionToReadOnlyMode();
            throw new IOException(e);
        }
    }

    public ByteBuf getExplicitLac(long ledgerId) throws IOException, Bookie.NoLedgerException {
        ByteBuf lac;
        LedgerDescriptor handle = handles.getReadOnlyHandle(ledgerId);
        synchronized (handle) {
            lac = handle.getExplicitLac();
        }
        return lac;
    }

    /**
     * Force sync given 'ledgerId' entries on the journal to the disk.
     * It works like a regular addEntry with ackBeforeSync=false.
     * This is useful for ledgers with DEFERRED_SYNC write flag.
     */
    public void forceLedger(long ledgerId, WriteCallback cb,
                            Object ctx) {
        if (LOG.isTraceEnabled()) {
            LOG.trace("Forcing ledger {}", ledgerId);
        }
        Journal journal = getJournal(ledgerId);
        journal.forceLedger(ledgerId, cb, ctx);
        bookieStats.getForceLedgerOps().inc();
    }

    /**
     * Add entry to a ledger.
     */
    public void addEntry(ByteBuf entry, boolean ackBeforeSync, WriteCallback cb, Object ctx, byte[] masterKey)
            throws IOException, BookieException, InterruptedException {
        long requestNanos = MathUtils.nowInNano();
        boolean success = false;
        int entrySize = 0;
        try {
            LedgerDescriptor handle = getLedgerForEntry(entry, masterKey);
            synchronized (handle) {
                if (handle.isFenced()) {
                    throw BookieException
                            .create(BookieException.Code.LedgerFencedException);
                }
                entrySize = entry.readableBytes();
                addEntryInternal(handle, entry, ackBeforeSync, cb, ctx, masterKey);
            }
            success = true;
        } catch (NoWritableLedgerDirException e) {
            stateManager.transitionToReadOnlyMode();
            throw new IOException(e);
        } finally {
            long elapsedNanos = MathUtils.elapsedNanos(requestNanos);
            if (success) {
                bookieStats.getAddEntryStats().registerSuccessfulEvent(elapsedNanos, TimeUnit.NANOSECONDS);
                bookieStats.getAddBytesStats().registerSuccessfulValue(entrySize);
            } else {
                bookieStats.getAddEntryStats().registerFailedEvent(elapsedNanos, TimeUnit.NANOSECONDS);
                bookieStats.getAddBytesStats().registerFailedValue(entrySize);
            }

            entry.release();
        }
    }

    /**
     * Fences a ledger. From this point on, clients will be unable to
     * write to this ledger. Only recoveryAddEntry will be
     * able to add entries to the ledger.
     * This method is idempotent. Once a ledger is fenced, it can
     * never be unfenced. Fencing a fenced ledger has no effect.
     * @return
     */
    public CompletableFuture<Boolean> fenceLedger(long ledgerId, byte[] masterKey)
            throws IOException, BookieException {
        LedgerDescriptor handle = handles.getHandle(ledgerId, masterKey);
        return handle.fenceAndLogInJournal(getJournal(ledgerId));
    }

    public ByteBuf readEntry(long ledgerId, long entryId)
            throws IOException, NoLedgerException {
        long requestNanos = MathUtils.nowInNano();
        boolean success = false;
        int entrySize = 0;
        try {
            LedgerDescriptor handle = handles.getReadOnlyHandle(ledgerId);
            if (LOG.isTraceEnabled()) {
                LOG.trace("Reading {}@{}", entryId, ledgerId);
            }
            ByteBuf entry = handle.readEntry(entryId);
            bookieStats.getReadBytes().add(entry.readableBytes());
            success = true;
            return entry;
        } finally {
            long elapsedNanos = MathUtils.elapsedNanos(requestNanos);
            if (success) {
                bookieStats.getReadEntryStats().registerSuccessfulEvent(elapsedNanos, TimeUnit.NANOSECONDS);
                bookieStats.getReadBytesStats().registerSuccessfulValue(entrySize);
            } else {
                bookieStats.getReadEntryStats().registerFailedEvent(elapsedNanos, TimeUnit.NANOSECONDS);
                bookieStats.getReadEntryStats().registerFailedValue(entrySize);
            }
        }
    }

    public long readLastAddConfirmed(long ledgerId) throws IOException {
        LedgerDescriptor handle = handles.getReadOnlyHandle(ledgerId);
        return handle.getLastAddConfirmed();
    }

    public boolean waitForLastAddConfirmedUpdate(long ledgerId,
                                                 long previousLAC,
                                                 Watcher<LastAddConfirmedUpdateNotification> watcher)
            throws IOException {
        LedgerDescriptor handle = handles.getReadOnlyHandle(ledgerId);
        return handle.waitForLastAddConfirmedUpdate(previousLAC, watcher);
    }

    public void cancelWaitForLastAddConfirmedUpdate(long ledgerId,
                                                    Watcher<LastAddConfirmedUpdateNotification> watcher)
            throws IOException {
        LedgerDescriptor handle = handles.getReadOnlyHandle(ledgerId);
        handle.cancelWaitForLastAddConfirmedUpdate(watcher);
    }

    @VisibleForTesting
    public LedgerStorage getLedgerStorage() {
        return ledgerStorage;
    }

    @VisibleForTesting
    public BookieStateManager getStateManager() {
        return (BookieStateManager) this.stateManager;
    }

    @VisibleForTesting
    public LedgerManagerFactory getLedgerManagerFactory() {
        return ledgerManagerFactory;
    }

    // The rest of the code is test stuff
    static class CounterCallback implements WriteCallback {
        int count;

        @Override
        public synchronized void writeComplete(int rc, long l, long e, BookieId addr, Object ctx) {
            count--;
            if (count == 0) {
                notifyAll();
            }
        }

        public synchronized void incCount() {
            count++;
        }

        public synchronized void waitZero() throws InterruptedException {
            while (count > 0) {
                wait();
            }
        }
    }

    public ByteBufAllocator getAllocator() {
        return allocator;
    }

    /**
     * Format the bookie server data.
     *
     * @param conf ServerConfiguration
     * @param isInteractive Whether format should ask prompt for confirmation if old data exists or not.
     * @param force If non interactive and force is true, then old data will be removed without confirm prompt.
     * @return Returns true if the format is success else returns false
     */
    public static boolean format(ServerConfiguration conf,
            boolean isInteractive, boolean force) {
        for (File journalDir : conf.getJournalDirs()) {
            String[] journalDirFiles =
                    journalDir.exists() && journalDir.isDirectory() ? journalDir.list() : null;
            if (journalDirFiles != null && journalDirFiles.length != 0) {
                try {
                    boolean confirm = false;
                    if (!isInteractive) {
                        // If non interactive and force is set, then delete old
                        // data.
                        confirm = force;
                    } else {
                        confirm = IOUtils
                                .confirmPrompt("Are you sure to format Bookie data..?");
                    }

                    if (!confirm) {
                        LOG.error("Bookie format aborted!!");
                        return false;
                    }
                } catch (IOException e) {
                    LOG.error("Error during bookie format", e);
                    return false;
                }
            }
            if (!cleanDir(journalDir)) {
                LOG.error("Formatting journal directory failed");
                return false;
            }
        }

        File[] ledgerDirs = conf.getLedgerDirs();
        for (File dir : ledgerDirs) {
            if (!cleanDir(dir)) {
                LOG.error("Formatting ledger directory " + dir + " failed");
                return false;
            }
        }

        // Clean up index directories if they are separate from the ledger dirs
        File[] indexDirs = conf.getIndexDirs();
        if (null != indexDirs) {
            for (File dir : indexDirs) {
                if (!cleanDir(dir)) {
                    LOG.error("Formatting index directory " + dir + " failed");
                    return false;
                }
            }
        }

        LOG.info("Bookie format completed successfully");
        return true;
    }

    private static boolean cleanDir(File dir) {
        if (dir.exists()) {
            File[] files = dir.listFiles();
            if (files != null) {
                for (File child : files) {
                    boolean delete = FileUtils.deleteQuietly(child);
                    if (!delete) {
                        LOG.error("Not able to delete " + child);
                        return false;
                    }
                }
            }
        } else if (!dir.mkdirs()) {
            LOG.error("Not able to create the directory " + dir);
            return false;
        }
        return true;
    }

    /**
     * Returns exit code - cause of failure.
     *
     * @return {@link ExitCode}
     */
    public int getExitCode() {
        return exitCode;
    }

    static DiskChecker createDiskChecker(ServerConfiguration conf) {
        return new DiskChecker(conf.getDiskUsageThreshold(), conf.getDiskUsageWarnThreshold());
    }

    static LedgerDirsManager createLedgerDirsManager(ServerConfiguration conf, DiskChecker diskChecker,
                                                     StatsLogger statsLogger) {
        return new LedgerDirsManager(conf, conf.getLedgerDirs(), diskChecker, statsLogger);
    }

    static LedgerDirsManager createIndexDirsManager(ServerConfiguration conf, DiskChecker diskChecker,
                                                    StatsLogger statsLogger, LedgerDirsManager fallback) {
        File[] idxDirs = conf.getIndexDirs();
        if (null == idxDirs) {
            return fallback;
        } else {
            return new LedgerDirsManager(conf, idxDirs, diskChecker, statsLogger);
        }
    }

    public OfLong getListOfEntriesOfLedger(long ledgerId) throws IOException, NoLedgerException {
        long requestNanos = MathUtils.nowInNano();
        boolean success = false;
        try {
            LedgerDescriptor handle = handles.getReadOnlyHandle(ledgerId);
            if (LOG.isTraceEnabled()) {
                LOG.trace("GetEntriesOfLedger {}", ledgerId);
            }
            OfLong entriesOfLedger = handle.getListOfEntriesOfLedger(ledgerId);
            success = true;
            return entriesOfLedger;
        } finally {
            long elapsedNanos = MathUtils.elapsedNanos(requestNanos);
            if (success) {
                bookieStats.getReadEntryStats().registerSuccessfulEvent(elapsedNanos, TimeUnit.NANOSECONDS);
            } else {
                bookieStats.getReadEntryStats().registerFailedEvent(elapsedNanos, TimeUnit.NANOSECONDS);
            }
        }
    }
}
