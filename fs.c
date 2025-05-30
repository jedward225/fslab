// clang-format off
#include "config.h"
// clang-format on

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <fuse.h>
#include <fuse/fuse.h>
#include <libgen.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>
#include <utime.h>

#include "disk.h"
#include "fs_opt.h"
#include "logger.h"

// 默认的文件和目录的标志
#define DIRMODE (S_IFDIR | 0755)
#define REGMODE (S_IFREG | 0644)

// 一些辅助宏定义
#define ceil_div(a, b) (((a) + (b) - 1) / (b))
#define max(a, b) ((a) > (b) ? (a) : (b))
#define min(a, b) ((a) < (b) ? (a) : (b))

// 文件系统布局和参数定义
#define INODE_COUNT 32768                    // 总inode数量
#define MAX_FILENAME_LEN 24                  // 最大文件名长度
#define DIRECT_POINTER_COUNT 12              // 直接指针数量
#define INDIRECT_POINTER_COUNT 2             // 间接指针数量
#define BIT_PER_INT 32                       // 每个int的位数
#define BITMAP_SIZE 1024                     // 位图大小（int数组长度）
#define ROOT_INODE 0                         // 根目录inode号

// 文件系统块布局
#define SUPER_BLOCK_START 0                  // 超级块起始位置
#define INODE_BITMAP_START 1                 // inode位图起始位置
#define DATA_BITMAP_START 2                  // 数据块位图起始位置（可能需要多个块）
#define INODE_TABLE_START 4                  // inode表起始位置

// 计算相关宏
#define INODE_SIZE (sizeof(INode))
#define INODE_PER_BLOCK (BLOCK_SIZE / INODE_SIZE)
#define DIR_ENTRY_SIZE (sizeof(DirEntry))
#define DIR_ENTRY_PER_BLOCK (BLOCK_SIZE / DIR_ENTRY_SIZE)
#define DATA_BLOCK_START (INODE_TABLE_START + ceil_div(INODE_COUNT, INODE_PER_BLOCK))
#define POINTER_PER_BLOCK (BLOCK_SIZE / sizeof(int))

// 位图操作宏
#define BITMAP_GET(bitmap, i) ((bitmap)[(i) / BIT_PER_INT] & (1 << ((i) % BIT_PER_INT)))
#define BITMAP_SET(bitmap, i) ((bitmap)[(i) / BIT_PER_INT] |= (1 << ((i) % BIT_PER_INT)))
#define BITMAP_CLEAR(bitmap, i) ((bitmap)[(i) / BIT_PER_INT] &= ~(1 << ((i) % BIT_PER_INT)))

// 数据结构定义
typedef struct SuperBlock {
    unsigned int blockSize;     // block size的大小
    fsblkcnt_t blockCount;      // 总block数量
    fsblkcnt_t freeBlockCount;  // 空闲的block数量
    fsblkcnt_t inodeCount;      // 总inode数量
    fsblkcnt_t freeInodeCount;  // 空闲inode的数量
    unsigned int maxFileName;   // 文件名长度上限
    unsigned int magic;         // 魔数，用于文件系统识别
} SuperBlock;

typedef int Bitmap[BITMAP_SIZE];

typedef struct INode {
    mode_t mode;                                    // 文件类型和权限
    off_t size;                                     // 文件大小
    time_t atime;                                   // 访问时间
    time_t mtime;                                   // 修改时间
    time_t ctime;                                   // 状态改变时间
    long atime_nsec;                                // 访问时间纳秒部分
    long mtime_nsec;                                // 修改时间纳秒部分
    long ctime_nsec;                                // 状态改变时间纳秒部分
    unsigned int blockCount;                        // 已分配的数据块数量
    int directPointers[DIRECT_POINTER_COUNT];       // 直接指针
    int indirectPointers[INDIRECT_POINTER_COUNT];   // 间接指针
} INode;

typedef struct DirEntry {
    int inodeNum;                           // inode号
    char filename[MAX_FILENAME_LEN + 1];    // 文件名，含结束符
} DirEntry;

// 全局变量
static SuperBlock g_superblock;

// 辅助函数声明
static int allocate_inode(void);
static int allocate_data_block(void);
static void free_inode(int inode_num);
static void free_data_block(int block_num);
static int read_inode(int inode_num, INode* inode);
static int write_inode(int inode_num, const INode* inode);
static int read_bitmap(int start_block, Bitmap bitmap);
static int write_bitmap(int start_block, const Bitmap bitmap);
static int find_inode_by_path(const char* path);
static int find_inode_in_dir(int dir_inode_num, const char* filename);
static char* get_filename_from_path(const char* path);
static char* get_parent_path(const char* path);
static int get_parent_inode(const char* path);
static int add_dir_entry(int dir_inode_num, const char* filename, int inode_num);
static int remove_dir_entry(int dir_inode_num, const char* filename);
static int read_data_block(int inode_num, int block_index, char* buffer);
static int write_data_block(int inode_num, int block_index, const char* buffer);

typedef struct FileNode {
    unsigned int fileSize;
    unsigned int fileBlock;
    unsigned int fileInode;
} FileNode;

// 辅助函数实现

// 读取位图
static int read_bitmap(int start_block, Bitmap bitmap) {
    char buffer[BLOCK_SIZE];
    if (disk_read(start_block, buffer) != 0) {
        return -1;
    }
    memcpy(bitmap, buffer, sizeof(Bitmap));
    return 0;
}

// 写入位图
static int write_bitmap(int start_block, const Bitmap bitmap) {
    char buffer[BLOCK_SIZE];
    memset(buffer, 0, BLOCK_SIZE);
    memcpy(buffer, bitmap, sizeof(Bitmap));
    return disk_write(start_block, buffer);
}

// 分配一个空闲的inode
static int allocate_inode(void) {
    Bitmap inode_bitmap;
    if (read_bitmap(INODE_BITMAP_START, inode_bitmap) != 0) {
        return -1;
    }
    
    // first-fit
    for (int i = 0; i < INODE_COUNT; i++) {
        if (!BITMAP_GET(inode_bitmap, i)) {
            // 找到空闲inode，标记为已使用
            BITMAP_SET(inode_bitmap, i);
            if (write_bitmap(INODE_BITMAP_START, inode_bitmap) != 0) {
                return -1;
            }
            
            // 更新超级块中的空闲inode计数
            g_superblock.freeInodeCount--;
            char buffer[BLOCK_SIZE]; // here we can use malloc, of course
            memcpy(buffer, &g_superblock, sizeof(SuperBlock));
            disk_write(SUPER_BLOCK_START, buffer);
            return i;
        }
    }
    return -1;
}

// 分配一个空闲的数据块
static int allocate_data_block(void) {
    // first-fit
    Bitmap data_bitmap;
    if (read_bitmap(DATA_BITMAP_START, data_bitmap) != 0) {
        return -1;
    }
    
    for (int i = 0; i < BITMAP_SIZE * BIT_PER_INT; i++) {
        if (!BITMAP_GET(data_bitmap, i)) {
            BITMAP_SET(data_bitmap, i);
            if (write_bitmap(DATA_BITMAP_START, data_bitmap) != 0) {
                return -1;
            }
            
            g_superblock.freeBlockCount--;
            char buffer[BLOCK_SIZE];
            memcpy(buffer, &g_superblock, sizeof(SuperBlock));
            disk_write(SUPER_BLOCK_START, buffer);
            
            return i;
        }
    }
    
    // 尝试第二个数据位图块
    if (read_bitmap(DATA_BITMAP_START + 1, data_bitmap) != 0) {
        return -1;
    }
    
    for (int i = 0; i < BITMAP_SIZE * BIT_PER_INT; i++) {
        if (!BITMAP_GET(data_bitmap, i)) {
            BITMAP_SET(data_bitmap, i);
            if (write_bitmap(DATA_BITMAP_START + 1, data_bitmap) != 0) {
                return -1;
            }
            
            // 更新超级块
            g_superblock.freeBlockCount--;
            char buffer[BLOCK_SIZE];
            memcpy(buffer, &g_superblock, sizeof(SuperBlock));
            disk_write(SUPER_BLOCK_START, buffer);
            
            return BITMAP_SIZE * BIT_PER_INT + i;
        }
    }
    
    return -1;
}

// 释放inode
static void free_inode(int inode_num) {
    if (inode_num < 0 || inode_num >= INODE_COUNT) {
        return;
    }
    
    Bitmap inode_bitmap;
    if (read_bitmap(INODE_BITMAP_START, inode_bitmap) == 0) {
        BITMAP_CLEAR(inode_bitmap, inode_num);
        write_bitmap(INODE_BITMAP_START, inode_bitmap);
        
        g_superblock.freeInodeCount++;
        char buffer[BLOCK_SIZE];
        memcpy(buffer, &g_superblock, sizeof(SuperBlock));
        disk_write(SUPER_BLOCK_START, buffer);
    }
}

// 释放数据块
static void free_data_block(int block_num) {
    if (block_num < 0) {
        return;
    }
    
    int bitmap_index, bit_index;
    Bitmap data_bitmap;
    
    if (block_num < BITMAP_SIZE * BIT_PER_INT) {
        // 在第一个位图块中
        bitmap_index = DATA_BITMAP_START;
        bit_index = block_num;
    } else {
        // 在第二个位图块中
        bitmap_index = DATA_BITMAP_START + 1;
        bit_index = block_num - BITMAP_SIZE * BIT_PER_INT;
    }
    
    if (read_bitmap(bitmap_index, data_bitmap) == 0) {
        BITMAP_CLEAR(data_bitmap, bit_index);
        write_bitmap(bitmap_index, data_bitmap);
        
        g_superblock.freeBlockCount++;
        char buffer[BLOCK_SIZE];
        memcpy(buffer, &g_superblock, sizeof(SuperBlock));
        disk_write(SUPER_BLOCK_START, buffer);
    }
}

// 读取inode
static int read_inode(int inode_num, INode* inode) {
    if (inode_num < 0 || inode_num >= INODE_COUNT || inode == NULL) {
        return -1;
    }
    
    int block_num = inode_num / INODE_PER_BLOCK;
    int offset = inode_num % INODE_PER_BLOCK;
    
    char buffer[BLOCK_SIZE];
    if (disk_read(INODE_TABLE_START + block_num, buffer) != 0) {
        return -1;
    }
    
    INode* inode_array = (INode*)buffer;
    *inode = inode_array[offset];
    return 0;
}

// 写入inode
static int write_inode(int inode_num, const INode* inode) {
    if (inode_num < 0 || inode_num >= INODE_COUNT || inode == NULL) {
        return -1;
    }
    
    int block_num = inode_num / INODE_PER_BLOCK;
    int offset = inode_num % INODE_PER_BLOCK;
    
    char buffer[BLOCK_SIZE];
    if (disk_read(INODE_TABLE_START + block_num, buffer) != 0) {
        return -1;
    }
    
    INode* inode_array = (INode*)buffer;
    inode_array[offset] = *inode;
    
    return disk_write(INODE_TABLE_START + block_num, buffer);
}

// 从路径中提取文件名
static char* get_filename_from_path(const char* path) {
    if (path == NULL || strlen(path) == 0) {
        return NULL;
    }
    
    // 处理根目录
    if (strcmp(path, "/") == 0) {
        return NULL;
    }
    
    char* path_copy = strdup(path);
    char* filename = strrchr(path_copy, '/');
    if (filename != NULL) {
        filename++; // 跳过 '/'
        char* result = strdup(filename);
        free(path_copy);
        return result;
    }
    
    free(path_copy);
    return NULL;
}

// 获取父目录路径
static char* get_parent_path(const char* path) {
    if (path == NULL || strlen(path) <= 1) {
        return NULL;
    }
    
    char* path_copy = strdup(path);
    char* last_slash = strrchr(path_copy, '/');
    
    if (last_slash == path_copy) {
        // 父目录是根目录
        free(path_copy);
        return strdup("/");
    } else if (last_slash != NULL) {
        *last_slash = '\0';
        char* result = strdup(path_copy);
        free(path_copy);
        return result;
    }
    
    free(path_copy);
    return NULL;
}

// 在目录中查找文件
static int find_inode_in_dir(int dir_inode_num, const char* filename) {
    INode dir_inode;
    if (read_inode(dir_inode_num, &dir_inode) != 0) {
        return -1;
    }
    
    if (!S_ISDIR(dir_inode.mode)) {
        return -1;
    }
    
    // 计算最大块数（包括间接指针）
    int max_blocks = DIRECT_POINTER_COUNT + INDIRECT_POINTER_COUNT * (BLOCK_SIZE / sizeof(int));
    int actual_max_blocks = min(max_blocks, dir_inode.blockCount);
    
    // 遍历所有数据块（包括间接指针）
    for (int i = 0; i < actual_max_blocks; i++) {
        char block_buffer[BLOCK_SIZE];
        if (read_data_block(dir_inode_num, i, block_buffer) != 0) {
            continue;
        }
        
        DirEntry* entries = (DirEntry*)block_buffer;
        int entries_per_block = BLOCK_SIZE / sizeof(DirEntry);
        
        for (int j = 0; j < entries_per_block; j++) {
            if (entries[j].inodeNum != -1 && strcmp(entries[j].filename, filename) == 0) {
                return entries[j].inodeNum;
            }
        }
    }
    
    return -1; // 未找到
}

// 根据路径查找inode号
static int find_inode_by_path(const char* path) {
    if (path == NULL) {
        return -1;
    }
    
    // 根目录
    if (strcmp(path, "/") == 0) {
        return ROOT_INODE;
    }
    
    // 解析路径
    char* path_copy = strdup(path);
    int current_inode = ROOT_INODE;
    
    char* token = strtok(path_copy, "/");
    while (token != NULL && current_inode != -1) {
        current_inode = find_inode_in_dir(current_inode, token);
        token = strtok(NULL, "/");
    }
    
    free(path_copy);
    return current_inode;
}

// 获取父目录的inode号
static int get_parent_inode(const char* path) {
    char* parent_path = get_parent_path(path);
    if (parent_path == NULL) {
        return -1;
    }
    
    int parent_inode = find_inode_by_path(parent_path);
    free(parent_path);
    return parent_inode;
}

// 向目录中添加目录项
static int add_dir_entry(int dir_inode_num, const char* filename, int inode_num) {
    INode dir_inode;
    if (read_inode(dir_inode_num, &dir_inode) != 0) {
        return -1;
    }
    
    // 检查是否是目录
    if (!S_ISDIR(dir_inode.mode)) {
        return -1;
    }
    
    // 查找空闲位置或分配新块
    for (int i = 0; i < DIRECT_POINTER_COUNT; i++) {
        if (dir_inode.directPointers[i] == -1) {
            // 需要分配新的数据块
            int new_block = allocate_data_block();
            if (new_block == -1) {
                return -1; // 没有足够空间
            }
            
            dir_inode.directPointers[i] = new_block;
            dir_inode.blockCount = i + 1;
            
            // 初始化新块
            char block_buffer[BLOCK_SIZE];
            memset(block_buffer, 0, BLOCK_SIZE);
            DirEntry* entries = (DirEntry*)block_buffer;
            
            // 初始化所有条目为无效
            int entries_per_block = BLOCK_SIZE / sizeof(DirEntry);
            for (int j = 0; j < entries_per_block; j++) {
                entries[j].inodeNum = -1;
            }
            
            // 添加新条目
            entries[0].inodeNum = inode_num;
            strncpy(entries[0].filename, filename, MAX_FILENAME_LEN);
            entries[0].filename[MAX_FILENAME_LEN] = '\0';
            
            // 写回数据块
            if (disk_write(DATA_BLOCK_START + new_block, block_buffer) != 0) {
                return -1;
            }
            
            // 更新目录大小和时间
            dir_inode.size += sizeof(DirEntry);
            struct timespec current_time;
            clock_gettime(CLOCK_REALTIME, &current_time);
            dir_inode.mtime = current_time.tv_sec;
            dir_inode.ctime = current_time.tv_sec;
            dir_inode.atime = current_time.tv_sec;
            dir_inode.atime_nsec = current_time.tv_nsec;
            dir_inode.mtime_nsec = current_time.tv_nsec;
            dir_inode.ctime_nsec = current_time.tv_nsec;
            
            // 写回inode
            return write_inode(dir_inode_num, &dir_inode);
        } else {
            // 检查已有块是否有空间
            char block_buffer[BLOCK_SIZE];
            if (disk_read(DATA_BLOCK_START + dir_inode.directPointers[i], block_buffer) != 0) {
                continue;
            }
            
            DirEntry* entries = (DirEntry*)block_buffer;
            int entries_per_block = BLOCK_SIZE / sizeof(DirEntry);
            
            for (int j = 0; j < entries_per_block; j++) {
                if (entries[j].inodeNum == -1) {
                    // 找到空闲位置
                    entries[j].inodeNum = inode_num;
                    strncpy(entries[j].filename, filename, MAX_FILENAME_LEN);
                    entries[j].filename[MAX_FILENAME_LEN] = '\0';
                    
                    // 写回数据块
                    if (disk_write(DATA_BLOCK_START + dir_inode.directPointers[i], block_buffer) != 0) {
                        return -1;
                    }
                    
                    // 更新目录大小和时间
                    dir_inode.size += sizeof(DirEntry);
                    struct timespec current_time;
                    clock_gettime(CLOCK_REALTIME, &current_time);
                    dir_inode.mtime = current_time.tv_sec;
                    dir_inode.ctime = current_time.tv_sec;
                    dir_inode.atime = current_time.tv_sec;
                    dir_inode.atime_nsec = current_time.tv_nsec;
                    dir_inode.mtime_nsec = current_time.tv_nsec;
                    dir_inode.ctime_nsec = current_time.tv_nsec;
                    
                    return write_inode(dir_inode_num, &dir_inode);
                }
            }
        }
    }
    
    // 如果所有直接指针块都已满，尝试使用间接指针
    // 检查是否可以分配新的间接指针块
    int max_blocks = DIRECT_POINTER_COUNT + INDIRECT_POINTER_COUNT * (BLOCK_SIZE / sizeof(int));
    
    for (int i = DIRECT_POINTER_COUNT; i < max_blocks; i++) {
        // 尝试分配新的数据块用于存储目录条目
        char block_buffer[BLOCK_SIZE];
        memset(block_buffer, 0, BLOCK_SIZE);
        
        DirEntry* entries = (DirEntry*)block_buffer;
        int entries_per_block = BLOCK_SIZE / sizeof(DirEntry);
        
        // 初始化所有条目为无效
        for (int j = 0; j < entries_per_block; j++) {
            entries[j].inodeNum = -1;
        }
        
        // 添加新条目到第一个位置
        entries[0].inodeNum = inode_num;
        strncpy(entries[0].filename, filename, MAX_FILENAME_LEN);
        entries[0].filename[MAX_FILENAME_LEN] = '\0';
        
        // 使用write_data_block来写入，这会自动处理间接指针分配
        if (write_data_block(dir_inode_num, i, block_buffer) == 0) {
            // 重新读取inode以获取更新的blockCount
            read_inode(dir_inode_num, &dir_inode);
            
            // 更新目录大小和时间
            dir_inode.size += sizeof(DirEntry);
            struct timespec current_time;
            clock_gettime(CLOCK_REALTIME, &current_time);
            dir_inode.mtime = current_time.tv_sec;
            dir_inode.ctime = current_time.tv_sec;
            dir_inode.atime = current_time.tv_sec;
            dir_inode.atime_nsec = current_time.tv_nsec;
            dir_inode.mtime_nsec = current_time.tv_nsec;
            dir_inode.ctime_nsec = current_time.tv_nsec;
            
            return write_inode(dir_inode_num, &dir_inode);
        }
    }
    
    return -1; // 目录已满
}

// 从目录中移除目录项
static int remove_dir_entry(int dir_inode_num, const char* filename) {
    INode dir_inode;
    if (read_inode(dir_inode_num, &dir_inode) != 0) {
        return -1;
    }
    
    // 计算最大块数（包括间接指针）
    int max_blocks = DIRECT_POINTER_COUNT + INDIRECT_POINTER_COUNT * (BLOCK_SIZE / sizeof(int));
    int actual_max_blocks = min(max_blocks, dir_inode.blockCount);
    
    // 遍历所有数据块（包括间接指针）
    for (int i = 0; i < actual_max_blocks; i++) {
        char block_buffer[BLOCK_SIZE];
        if (read_data_block(dir_inode_num, i, block_buffer) != 0) {
            continue;
        }
        
        DirEntry* entries = (DirEntry*)block_buffer;
        int entries_per_block = BLOCK_SIZE / sizeof(DirEntry);
        
        for (int j = 0; j < entries_per_block; j++) {
            if (entries[j].inodeNum != -1 && strcmp(entries[j].filename, filename) == 0) {
                // 找到要删除的条目
                entries[j].inodeNum = -1;
                memset(entries[j].filename, 0, MAX_FILENAME_LEN + 1);
                
                // 写回数据块
                if (write_data_block(dir_inode_num, i, block_buffer) != 0) {
                    return -1;
                }
                
                // 更新目录时间
                struct timespec current_time;
                clock_gettime(CLOCK_REALTIME, &current_time);
                dir_inode.mtime = current_time.tv_sec;
                dir_inode.ctime = current_time.tv_sec;
                dir_inode.atime = current_time.tv_sec;
                dir_inode.atime_nsec = current_time.tv_nsec;
                dir_inode.mtime_nsec = current_time.tv_nsec;
                dir_inode.ctime_nsec = current_time.tv_nsec;
                
                return write_inode(dir_inode_num, &dir_inode);
            }
        }
    }
    
    return -1; // 未找到要删除的条目
}

// 读取文件的指定数据块
static int read_data_block(int inode_num, int block_index, char* buffer) {
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -1;
    }
    
    int block_num = -1;
    
    if (block_index < DIRECT_POINTER_COUNT) {
        // 直接指针
        block_num = inode.directPointers[block_index];
    } else {
        // 间接指针
        int indirect_index = block_index - DIRECT_POINTER_COUNT;
        int indirect_block_index = indirect_index / (BLOCK_SIZE / sizeof(int));
        int offset_in_indirect = indirect_index % (BLOCK_SIZE / sizeof(int));
        
        if (indirect_block_index >= INDIRECT_POINTER_COUNT) {
            return -1; // 超出支持范围
        }
        
        // 检查间接指针块是否已分配
        if (inode.indirectPointers[indirect_block_index] == -1) {
            // 块未分配，返回全零
            memset(buffer, 0, BLOCK_SIZE);
            return 0;
        }
        
        // 读取间接指针块
        int indirect_data[BLOCK_SIZE / sizeof(int)];
        if (disk_read(DATA_BLOCK_START + inode.indirectPointers[indirect_block_index], indirect_data) != 0) {
            return -1;
        }
        
        block_num = indirect_data[offset_in_indirect];
    }
    
    if (block_num == -1) {
        // 块未分配，返回全零
        memset(buffer, 0, BLOCK_SIZE);
        return 0;
    }
    
    return disk_read(DATA_BLOCK_START + block_num, buffer);
}

// 写入文件的指定数据块
static int write_data_block(int inode_num, int block_index, const char* buffer) {
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -1;
    }
    
    int block_num = -1;
    
    if (block_index < DIRECT_POINTER_COUNT) {
        // 直接指针
        if (inode.directPointers[block_index] == -1) {
            // 需要分配新块
            int new_block = allocate_data_block();
            if (new_block == -1) {
                return -1;
            }
            inode.directPointers[block_index] = new_block;
            inode.blockCount = max(inode.blockCount, block_index + 1);
            write_inode(inode_num, &inode);
        }
        block_num = inode.directPointers[block_index];
    } else {
        // 间接指针
        int indirect_index = block_index - DIRECT_POINTER_COUNT;
        int indirect_block_index = indirect_index / (BLOCK_SIZE / sizeof(int));
        int offset_in_indirect = indirect_index % (BLOCK_SIZE / sizeof(int));
        
        if (indirect_block_index >= INDIRECT_POINTER_COUNT) {
            return -1; // 超出支持范围
        }
        
        // 检查间接指针块是否已分配
        if (inode.indirectPointers[indirect_block_index] == -1) {
            int new_indirect_block = allocate_data_block();
            if (new_indirect_block == -1) {
                return -1;
            }
            inode.indirectPointers[indirect_block_index] = new_indirect_block;
            
            // 初始化间接指针块
            int indirect_data[BLOCK_SIZE / sizeof(int)];
            for (int i = 0; i < BLOCK_SIZE / sizeof(int); i++) {
                indirect_data[i] = -1;
            }
            disk_write(DATA_BLOCK_START + new_indirect_block, indirect_data);
            write_inode(inode_num, &inode);
        }
        
        // 读取间接指针块
        int indirect_data[BLOCK_SIZE / sizeof(int)];
        if (disk_read(DATA_BLOCK_START + inode.indirectPointers[indirect_block_index], indirect_data) != 0) {
            return -1;
        }
        
        // 检查对应的数据块是否已分配
        if (indirect_data[offset_in_indirect] == -1) {
            int new_data_block = allocate_data_block();
            if (new_data_block == -1) {
                return -1;
            }
            indirect_data[offset_in_indirect] = new_data_block;
            
            // 写回间接指针块
            if (disk_write(DATA_BLOCK_START + inode.indirectPointers[indirect_block_index], indirect_data) != 0) {
                return -1;
            }
            
            // 更新inode的块计数
            inode.blockCount = max(inode.blockCount, block_index + 1);
            write_inode(inode_num, &inode);
        }
        
        block_num = indirect_data[offset_in_indirect];
    }
    
    return disk_write(DATA_BLOCK_START + block_num, (void*)buffer);
}

// 释放inode的所有数据块
static void free_inode_blocks(int inode_num) {
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return;
    }
    
    // 释放直接指针指向的数据块
    for (int i = 0; i < DIRECT_POINTER_COUNT; i++) {
        if (inode.directPointers[i] != -1) {
            free_data_block(inode.directPointers[i]);
        }
    }
    
    // 释放间接指针指向的数据块
    for (int i = 0; i < INDIRECT_POINTER_COUNT; i++) {
        if (inode.indirectPointers[i] != -1) {
            // 读取间接指针块
            int indirect_data[BLOCK_SIZE / sizeof(int)];
            if (disk_read(DATA_BLOCK_START + inode.indirectPointers[i], indirect_data) == 0) {
                // 释放间接指针块中指向的所有数据块
                for (int j = 0; j < BLOCK_SIZE / sizeof(int); j++) {
                    if (indirect_data[j] != -1) {
                        free_data_block(indirect_data[j]);
                    }
                }
            }
            // 释放间接指针块本身
            free_data_block(inode.indirectPointers[i]);
        }
    }
}

// 检查目录是否为空
static int is_directory_empty(int dir_inode_num) {
    INode dir_inode;
    if (read_inode(dir_inode_num, &dir_inode) != 0) {
        return -1;
    }
    
    if (!S_ISDIR(dir_inode.mode)) {
        return -1;
    }
    
    // 计算最大块数（包括间接指针）
    int max_blocks = DIRECT_POINTER_COUNT + INDIRECT_POINTER_COUNT * (BLOCK_SIZE / sizeof(int));
    int actual_max_blocks = min(max_blocks, dir_inode.blockCount);
    
    // 遍历所有数据块（包括间接指针），检查是否只有无效条目
    for (int i = 0; i < actual_max_blocks; i++) {
        char block_buffer[BLOCK_SIZE];
        if (read_data_block(dir_inode_num, i, block_buffer) != 0) {
            continue;
        }
        
        DirEntry* entries = (DirEntry*)block_buffer;
        int entries_per_block = BLOCK_SIZE / sizeof(DirEntry);
        
        for (int j = 0; j < entries_per_block; j++) {
            if (entries[j].inodeNum != -1) {
                return 0; // 目录不为空
            }
        }
    }
    
    return 1; // 目录为空
}

// 初始化文件系统
//
// 参考实现：
// 当 init_flag 为 1 时，你应该：
// 1. 初始化一个超级块记录必要的参数
// 2. 初始化根节点，bitmap
//
// 当 init_flag 为 0 时，你应该：
// 1. 加载超级快
//
// 提示：
// 1. 由于我们没有脚本测试自定义初始化文件系统的参数，
// 所以你可以假设文件系统的参数是固定的，此时其实可以不要超级块（如果你确实不需要）
// 2. 如果你打算实现一个可以自定义初始化参数的文件系统，
// 你可以用环境变量来传递参数，或者参考 `fs_opt.c` 中的实现方法
/*
fs_opt.c
int has_noinit_flag(int *argc_ptr, char *argv[]) {
  int argc = *argc_ptr;
  int init_flag = 0;
  for (int i = 1; i < argc; i++) {
    if (!init_flag) {
      if (strcmp(argv[i], "--noinit") == 0) {
        init_flag = 1;
      }
    }
    if (init_flag && i < argc - 1) {
      argv[i] = argv[i + 1];
    }
  }
  *argc_ptr = argc - init_flag;
  return init_flag;
}
*/
int fs_mount(int init_flag) {
    fs_info("fs_mount is called\tinit_flag:%d)\n", init_flag);
    if (init_flag) {
        // 当 init_flag 为 1 时，你应该：
        // 1. 初始化一个超级块记录必要的参数
        // 2. 初始化根节点，bitmap
        g_superblock.blockSize = BLOCK_SIZE;
        g_superblock.blockCount = BLOCK_NUM;
        g_superblock.freeBlockCount = BLOCK_NUM - DATA_BLOCK_START; // 减去元数据占用的块
        g_superblock.inodeCount = INODE_COUNT;
        g_superblock.freeInodeCount = INODE_COUNT;
        g_superblock.maxFileName = MAX_FILENAME_LEN;
        g_superblock.magic = 0x12345678; // 魔数 whatever is okay
        
        // 写入超级块到磁盘
        char buffer[BLOCK_SIZE];
        memcpy(buffer, &g_superblock, sizeof(SuperBlock));
        if (disk_write(SUPER_BLOCK_START, buffer) != 0) {
            fs_error("Failed to write superblock\n");
            return -1;
        }
        
        // 初始化inode位图
        Bitmap inode_bitmap;
        memset(inode_bitmap, 0, sizeof(Bitmap));
        if (write_bitmap(INODE_BITMAP_START, inode_bitmap) != 0) {
            fs_error("Failed to write inode bitmap\n");
            return -1;
        }
        
        // 初始化数据块位图
        Bitmap data_bitmap;
        memset(data_bitmap, 0, sizeof(Bitmap));
        if (write_bitmap(DATA_BITMAP_START, data_bitmap) != 0) {
            fs_error("Failed to write data bitmap\n");
            return -1;
        }
        
        // 如果需要多个数据位图块，继续初始化
        if (write_bitmap(DATA_BITMAP_START + 1, data_bitmap) != 0) {
            fs_error("Failed to write second data bitmap\n");
            return -1;
        }
        
        // 初始化inode表区域为0
        memset(buffer, 0, BLOCK_SIZE);
        int inode_table_blocks = ceil_div(INODE_COUNT, INODE_PER_BLOCK);
        for (int i = 0; i < inode_table_blocks; i++) {
            if (disk_write(INODE_TABLE_START + i, buffer) != 0) {
                fs_error("Failed to initialize inode table block %d\n", i);
                return -1;
            }
        }
        
        // 初始化根目录
        // 分配根目录的inode
        int root_inode_num = allocate_inode();
        if (root_inode_num != ROOT_INODE) {
            fs_error("Failed to allocate root inode at expected position\n");
            return -1;
        }
        
        // 创建根目录inode
        INode root_inode;
        root_inode.mode = DIRMODE;
        root_inode.size = 0;
        struct timespec current_time;
        clock_gettime(CLOCK_REALTIME, &current_time);
        root_inode.atime = current_time.tv_sec;
        root_inode.mtime = current_time.tv_sec;
        root_inode.ctime = current_time.tv_sec;
        root_inode.atime_nsec = current_time.tv_nsec;
        root_inode.mtime_nsec = current_time.tv_nsec;
        root_inode.ctime_nsec = current_time.tv_nsec;
        root_inode.blockCount = 0;
        
        // 初始化指针为-1（无效）
        for (int i = 0; i < DIRECT_POINTER_COUNT; i++) {
            root_inode.directPointers[i] = -1;
        }
        for (int i = 0; i < INDIRECT_POINTER_COUNT; i++) {
            root_inode.indirectPointers[i] = -1;
        }
        
        // 写入根目录inode
        if (write_inode(ROOT_INODE, &root_inode) != 0) {
            fs_error("Failed to write root inode\n");
            return -1;
        }
        
    } else {
        // 加载超级块
        char buffer[BLOCK_SIZE];
        if (disk_read(SUPER_BLOCK_START, buffer) != 0) {
            fs_error("Failed to read superblock\n");
            return -1;
        }
        
        memcpy(&g_superblock, buffer, sizeof(SuperBlock));
        
        // 验证魔数
        if (g_superblock.magic != 0x12345678) {
            fs_error("Invalid filesystem magic number\n");
            return -1;
        }
        
        fs_info("Loaded filesystem: blocks=%ld, free_blocks=%ld, inodes=%ld, free_inodes=%ld\n",
                g_superblock.blockCount, g_superblock.freeBlockCount,
                g_superblock.inodeCount, g_superblock.freeInodeCount);
    }
    return 0;
}

// 关闭文件系统前的清理工作
//
// 如果你有一些工作要在文件系统被完全关闭前完成，比如确保所有数据都被写入磁盘，或是释放内存，请在
// fs_finalize 函数中完成，你可以假设 fuse_status 永远为 0，即 fuse
// 永远会正常退出，该函数当且仅当清理工作失败时返回非零值
int fs_finalize(int fuse_status) {
    // 确保超级块被正确写入磁盘
    char buffer[BLOCK_SIZE];
    memcpy(buffer, &g_superblock, sizeof(SuperBlock));
    if (disk_write(SUPER_BLOCK_START, buffer) != 0) {
        fs_error("Failed to write final superblock\n");
        return -1;
    }
    
    fs_info("Filesystem finalized successfully\n");
    return fuse_status;
}

// 查询一个文件或目录的属性
//
// 错误处理：
// 1. 条目不存在时返回 -ENOENT
//
// 参考实现：
// 1. 根据 path 从根目录开始遍历，找到 inode
// 2. 通过 inode 中存储的信息，填充 attr 结构体
//
// 提示：
// 1. 所有接口中的 path 都是相对于该文件系统根目录开始的绝对路径，相关的讨论见
// README.md
//
// `stat` 会触发该函数，实际上 `cd` 的时候也会触发，这个函数被触发的情景特别多
int fs_getattr(const char* path, struct stat* attr) {
    fs_info("fs_getattr is called:%s\n", path);

    // 根据路径查找inode
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 填充stat结构体
    memset(attr, 0, sizeof(struct stat));
    attr->st_mode = inode.mode;
    attr->st_nlink = 1;
    attr->st_uid = getuid();
    attr->st_gid = getgid();
    attr->st_size = inode.size;
    attr->st_atime = inode.atime;
    attr->st_mtime = inode.mtime;
    attr->st_ctime = inode.ctime;
    attr->st_blksize = BLOCK_SIZE;
    
    // 设置纳秒级时间戳
    attr->st_atim.tv_sec = inode.atime;
    attr->st_atim.tv_nsec = inode.atime_nsec;
    attr->st_mtim.tv_sec = inode.mtime;
    attr->st_mtim.tv_nsec = inode.mtime_nsec;
    attr->st_ctim.tv_sec = inode.ctime;
    attr->st_ctim.tv_nsec = inode.ctime_nsec;
    
    // 计算实际占用的512字节块数
    // st_blocks是以512字节为单位的
    attr->st_blocks = (inode.blockCount * BLOCK_SIZE + 511) / 512;

    return 0;
}

// 查询一个目录下的所有条目名（文件，目录）（忽略 offset 参数）
//
// 错误处理：
// 1. 目录不存在时返回 -ENOENT
//
// 参考实现：
// 1. 根据 path 从根目录开始遍历，找到 inode
// 2. 遍历该 inode（目录）下的所有条目（文件，目录），
// 对每一个条目名（文件名，目录名）name，调用 filler(buffer, name, NULL, 0)
// 3. 修改被查询目录的 atime（即被查询 inode 的 atime）
//
// `ls` 命令会触发这个函数
int fs_readdir(const char* path, void* buffer, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info* fi) {
    fs_info("fs_readdir is called:%s\n", path);

    // 根据路径查找inode
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是目录
    if (!S_ISDIR(inode.mode)) {
        return -ENOTDIR;
    }
    
    // 添加 . 和 .. 条目
    filler(buffer, ".", NULL, 0);
    filler(buffer, "..", NULL, 0);
    
    // 计算最大块数（包括间接指针）
    int max_blocks = DIRECT_POINTER_COUNT + INDIRECT_POINTER_COUNT * (BLOCK_SIZE / sizeof(int));
    int actual_max_blocks = min(max_blocks, inode.blockCount);
    
    // 遍历所有数据块（包括间接指针）
    for (int i = 0; i < actual_max_blocks; i++) {
        char block_buffer[BLOCK_SIZE];
        if (read_data_block(inode_num, i, block_buffer) != 0) {
            continue;
        }
        
        DirEntry* entries = (DirEntry*)block_buffer;
        int entries_per_block = BLOCK_SIZE / sizeof(DirEntry);
        
        for (int j = 0; j < entries_per_block; j++) {
            if (entries[j].inodeNum != -1) {
                filler(buffer, entries[j].filename, NULL, 0);
            }
        }
    }
    
    // 更新访问时间
    struct timespec current_time;
    clock_gettime(CLOCK_REALTIME, &current_time);
    inode.atime = current_time.tv_sec;
    inode.atime_nsec = current_time.tv_nsec;
    write_inode(inode_num, &inode);

    return 0;
}

// 从 offset 位置开始读取至多 size 字节内容到 buffer 中
//
// 错误处理：
// 文件不存在时返回 -ENOENT
//
// 参考实现：
// 1. 通过 path 找到 inode，或者通过之前 fs_open 记录的 fi->fh 直接找到 inode
// 2. 读取从 offset 开始的 size 字节内容到 buffer 中，但是不能超过 inode->size
// 3. 更新 inode 的 atime
// 4. 返回实际读取的字节数
//
// `cat` 命令会触发这个函数
int fs_read(const char* path, char* buffer, size_t size, off_t offset, struct fuse_file_info* fi) {
    fs_info("fs_read is called:%s\tsize:%zu\toffset:%ld\n", path, size, offset);

    // 根据路径查找inode
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是文件
    if (!S_ISREG(inode.mode)) {
        return -EISDIR;
    }
    
    // 检查读取偏移是否超出文件大小
    if (offset >= inode.size) {
        return 0; // 到达文件末尾
    }
    
    // 调整读取大小，不要超出文件范围
    if (offset + size > inode.size) {
        size = inode.size - offset;
    }
    
    size_t bytes_read = 0;
    int start_block = offset / BLOCK_SIZE;
    int start_offset = offset % BLOCK_SIZE;
    
    while (bytes_read < size) {
        char block_buffer[BLOCK_SIZE];
        int block_index = start_block + (bytes_read + start_offset) / BLOCK_SIZE;
        
        // 读取数据块
        if (read_data_block(inode_num, block_index, block_buffer) != 0) {
            break; // 读取失败
        }
        
        // 计算在当前块中的读取位置和大小
        int block_offset = (offset + bytes_read) % BLOCK_SIZE;
        size_t bytes_to_read = min(BLOCK_SIZE - block_offset, size - bytes_read);
        
        // 复制数据到输出缓冲区
        memcpy(buffer + bytes_read, block_buffer + block_offset, bytes_to_read);
        bytes_read += bytes_to_read;
    }
    
    // 更新访问时间
    struct timespec current_time;
    clock_gettime(CLOCK_REALTIME, &current_time);
    inode.atime = current_time.tv_sec;
    inode.atime_nsec = current_time.tv_nsec;
    write_inode(inode_num, &inode);
    
    return bytes_read;
}

// 创建一个文件（忽略 mode 和 dev 参数）
//
// 错误处理：
// 1. 文件已存在时返回 -EEXIST
// 2. 没有足够的空间时返回 -ENOSPC
//
// 参考实现：
// 1. 通过 path 找到其父目录的 inode
// 2. 创建并初始化一个新的 inode，其为 stat 记录的 `st_mode` 为 `REGMODE`
// 3. 在父目录的 inode 中添加一个新的目录项，指向新创建的 inode
// 4. 更新父目录的 inode 的 mtime，ctime
//
// `touch` 命令会触发这个函数
int fs_mknod(const char* path, mode_t mode, dev_t dev) {
    fs_info("fs_mknod is called:%s\n", path);

    // 检查文件是否已存在
    if (find_inode_by_path(path) != -1) {
        return -EEXIST;
    }
    
    // 获取父目录
    int parent_inode_num = get_parent_inode(path);
    if (parent_inode_num == -1) {
        return -ENOENT; // 父目录不存在
    }
    
    // 获取文件名
    char* filename = get_filename_from_path(path);
    if (filename == NULL) {
        return -EINVAL;
    }
    
    // 检查文件名长度
    if (strlen(filename) > MAX_FILENAME_LEN) {
        free(filename);
        return -ENAMETOOLONG;
    }
    
    // 分配新的inode
    int new_inode_num = allocate_inode();
    if (new_inode_num == -1) {
        free(filename);
        return -ENOSPC; // 没有足够的inode
    }
    
    // 创建并初始化新的inode
    INode new_inode;
    new_inode.mode = REGMODE;
    new_inode.size = 0;
    struct timespec current_time;
    clock_gettime(CLOCK_REALTIME, &current_time);
    new_inode.atime = current_time.tv_sec;
    new_inode.mtime = current_time.tv_sec;
    new_inode.ctime = current_time.tv_sec;
    new_inode.atime_nsec = current_time.tv_nsec;
    new_inode.mtime_nsec = current_time.tv_nsec;
    new_inode.ctime_nsec = current_time.tv_nsec;
    new_inode.blockCount = 0;
    
    // 初始化指针为-1（无效）
    for (int i = 0; i < DIRECT_POINTER_COUNT; i++) {
        new_inode.directPointers[i] = -1;
    }
    for (int i = 0; i < INDIRECT_POINTER_COUNT; i++) {
        new_inode.indirectPointers[i] = -1;
    }
    
    // 写入新的inode
    if (write_inode(new_inode_num, &new_inode) != 0) {
        free_inode(new_inode_num);
        free(filename);
        return -EIO;
    }
    
    // 在父目录中添加新的目录项
    if (add_dir_entry(parent_inode_num, filename, new_inode_num) != 0) {
        free_inode(new_inode_num);
        free(filename);
        return -ENOSPC; // 目录空间不足
    }
    
    free(filename);
    return 0;
}

// 创建一个目录（忽略 mode 参数）
//
// 和 fs_mknod 几乎一模一样，
// 唯一的区别是其对应的 stat 记录的 `st_mode` 为 `DIRMODE`
int fs_mkdir(const char* path, mode_t mode) {
    fs_info("fs_mkdir is called:%s\n", path);

    // 检查目录是否已存在
    if (find_inode_by_path(path) != -1) {
        return -EEXIST;
    }
    
    // 获取父目录
    int parent_inode_num = get_parent_inode(path);
    if (parent_inode_num == -1) {
        return -ENOENT; // 父目录不存在
    }
    
    // 获取目录名
    char* dirname = get_filename_from_path(path);
    if (dirname == NULL) {
        return -EINVAL;
    }
    
    // 检查目录名长度
    if (strlen(dirname) > MAX_FILENAME_LEN) {
        free(dirname);
        return -ENAMETOOLONG;
    }
    
    // 分配新的inode
    int new_inode_num = allocate_inode();
    if (new_inode_num == -1) {
        free(dirname);
        return -ENOSPC; // 没有足够的inode
    }
    
    // 创建并初始化新的目录inode
    INode new_inode;
    new_inode.mode = DIRMODE;
    new_inode.size = 0;
    struct timespec current_time;
    clock_gettime(CLOCK_REALTIME, &current_time);
    new_inode.atime = current_time.tv_sec;
    new_inode.mtime = current_time.tv_sec;
    new_inode.ctime = current_time.tv_sec;
    new_inode.atime_nsec = current_time.tv_nsec;
    new_inode.mtime_nsec = current_time.tv_nsec;
    new_inode.ctime_nsec = current_time.tv_nsec;
    new_inode.blockCount = 0;
    
    // 初始化指针为-1（无效）
    for (int i = 0; i < DIRECT_POINTER_COUNT; i++) {
        new_inode.directPointers[i] = -1;
    }
    for (int i = 0; i < INDIRECT_POINTER_COUNT; i++) {
        new_inode.indirectPointers[i] = -1;
    }
    
    // 写入新的inode
    if (write_inode(new_inode_num, &new_inode) != 0) {
        free_inode(new_inode_num);
        free(dirname);
        return -EIO;
    }
    
    // 在父目录中添加新的目录项
    if (add_dir_entry(parent_inode_num, dirname, new_inode_num) != 0) {
        free_inode(new_inode_num);
        free(dirname);
        return -ENOSPC; // 目录空间不足
    }
    
    free(dirname);
    return 0;
}

// 删除一个文件
//
// 错误处理：
// 1. 文件不存在时返回 -ENOENT
//
// 参考实现：
// 1. 通过 path 找到其父目录的 inode，记作 parent_inode
// 2. 在 parent_inode 中删除该文件的 inode，记该 inode 为 child_inode
// 3. 遍历 child_inode 的 data_block 标记释放，最后标记释放 child_inode
// 4. 更新 parent_inode 的 mtime，ctime
//
// `rm` 命令会触发该函数
int fs_unlink(const char* path) {
    fs_info("fs_unlink is callded:%s\n", path);

    // 查找要删除的文件
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是文件（不是目录）
    if (S_ISDIR(inode.mode)) {
        return -EISDIR;
    }
    
    // 获取父目录
    int parent_inode_num = get_parent_inode(path);
    if (parent_inode_num == -1) {
        return -ENOENT;
    }
    
    // 获取文件名
    char* filename = get_filename_from_path(path);
    if (filename == NULL) {
        return -EINVAL;
    }
    
    // 从父目录中删除目录项
    if (remove_dir_entry(parent_inode_num, filename) != 0) {
        free(filename);
        return -ENOENT;
    }
    
    // 释放文件的所有数据块
    free_inode_blocks(inode_num);
    
    // 释放inode
    free_inode(inode_num);
    
    free(filename);
    return 0;
}

// 删除一个目录
//
// 和 `fs_unlink` 的实现几乎一模一样
//
// 提示：
// 1. 调用该接口时系统会保证该目录下为空
// （即查询你实现的 readdir ，返回的内容为空）
//
// `rmdir` 命令会触发该函数
// 事实上，`rm -rf` 时的处理方法是系统自己调用 `ls, cd, rm, rmdir`
// 来处理递归删除，而不是交给文件系统来处理递归
int fs_rmdir(const char* path) {
    fs_info("fs_rmdir is called:%s\n", path);

    // 不允许删除根目录
    if (strcmp(path, "/") == 0) {
        return -EBUSY;
    }
    
    // 查找要删除的目录
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是目录
    if (!S_ISDIR(inode.mode)) {
        return -ENOTDIR;
    }
    
    // 检查目录是否为空
    int empty_result = is_directory_empty(inode_num);
    if (empty_result < 0) {
        return -EIO;
    }
    if (empty_result == 0) {
        return -ENOTEMPTY;
    }
    
    // 获取父目录
    int parent_inode_num = get_parent_inode(path);
    if (parent_inode_num == -1) {
        return -ENOENT;
    }
    
    // 获取目录名
    char* dirname = get_filename_from_path(path);
    if (dirname == NULL) {
        return -EINVAL;
    }
    
    // 从父目录中删除目录项
    if (remove_dir_entry(parent_inode_num, dirname) != 0) {
        free(dirname);
        return -ENOENT;
    }
    
    // 释放目录的所有数据块
    free_inode_blocks(inode_num);
    
    // 释放inode
    free_inode(inode_num);
    
    free(dirname);
    return 0;
}

// 移动一个条目（文件或目录）
//
// 错误处理：
// 略
//
// 参考实现：
// 一个代码复用性比较好的实现方式是
// 1. 先做一个不标记释放 data block 的 fs_unlink
// 2. 做一个用已有 inode 的 fs_mknod
// （即原本是创建一个新的 inode，现在是用 oldpath 对应的那个）
// 3. 记得同时更新新旧父目录的 mtime
//
// 思考：
// 1. 如果移动的是目录，目录下的内容要怎么处理
//
// `mv` 命令会触发该函数
int fs_rename(const char* oldpath, const char* newpath) {
    fs_info("fs_rename is called:%s\tnewpath:%s\n", oldpath, newpath);

    // 查找源文件/目录
    int old_inode_num = find_inode_by_path(oldpath);
    if (old_inode_num == -1) {
        return -ENOENT;
    }
    
    // 检查目标是否已存在
    if (find_inode_by_path(newpath) != -1) {
        return -EEXIST;
    }
    
    // 获取源文件的父目录
    int old_parent_inode_num = get_parent_inode(oldpath);
    if (old_parent_inode_num == -1) {
        return -ENOENT;
    }
    
    // 获取目标文件的父目录
    int new_parent_inode_num = get_parent_inode(newpath);
    if (new_parent_inode_num == -1) {
        return -ENOENT;
    }
    
    // 获取源文件名和目标文件名
    char* old_filename = get_filename_from_path(oldpath);
    char* new_filename = get_filename_from_path(newpath);
    if (old_filename == NULL || new_filename == NULL) {
        if (old_filename) free(old_filename);
        if (new_filename) free(new_filename);
        return -EINVAL;
    }
    
    // 检查新文件名长度
    if (strlen(new_filename) > MAX_FILENAME_LEN) {
        free(old_filename);
        free(new_filename);
        return -ENAMETOOLONG;
    }
    
    // 在新位置添加目录项
    if (add_dir_entry(new_parent_inode_num, new_filename, old_inode_num) != 0) {
        free(old_filename);
        free(new_filename);
        return -ENOSPC;
    }
    
    // 从旧位置删除目录项
    if (remove_dir_entry(old_parent_inode_num, old_filename) != 0) {
        // 如果删除失败，需要回滚新位置的添加
        remove_dir_entry(new_parent_inode_num, new_filename);
        free(old_filename);
        free(new_filename);
        return -ENOENT;
    }
    
    // 更新inode的ctime
    INode inode;
    if (read_inode(old_inode_num, &inode) == 0) {
        inode.ctime = time(NULL);
        write_inode(old_inode_num, &inode);
    }
    
    free(old_filename);
    free(new_filename);
    return 0;
}

// 从 offset 开始写入 size 字节的内容到文件中
//
// 错误处理：
// 1. 文件不存在时返回 -ENOENT
// 2. 没有足够的空间时返回 -ENOSPC
// 3. 超过单文件大小限制时返回 -EFBIG
//
// 参考实现：
// 1. 通过 path 找到 inode，或者通过之前 fs_open 记录的 fi->fh 直接找到 inode
// 2. 如果 fi->flags 中有 O_APPEND 标志，设置 offset 到文件末尾
// 3. 如果写入后的文件大小超过已经分配的数据块大小，新分配足够的数据块
// 4. 遍历 inode 的所有数据块，找到并修改对应的数据块
// 5. 更新 inode 的 mtime，ctime
// 6. 返回实际写入的字节数
//
// `echo "hello world" > test.txt` 命令会触发这个函数
int fs_write(const char* path, const char* buffer, size_t size, off_t offset, struct fuse_file_info* fi) {
    fs_info("fs_write is called:%s\tsize:%zu\toffset:%ld\n", path, size, offset);

    // 查找文件
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是文件
    if (!S_ISREG(inode.mode)) {
        return -EISDIR;
    }
    
    // 处理O_APPEND标志
    if (fi && (fi->flags & O_APPEND)) {
        offset = inode.size;
    }
    
    // 检查是否超过单文件大小限制
    // 直接指针：12 * 4KB = 48KB
    // 间接指针：2 * 1024 * 4KB = 8MB
    // 总计：48KB + 8MB ≈ 8MB
    int max_blocks = DIRECT_POINTER_COUNT + INDIRECT_POINTER_COUNT * (BLOCK_SIZE / sizeof(int));
    if (offset + size > max_blocks * BLOCK_SIZE) {
        return -EFBIG;
    }
    
    size_t bytes_written = 0;
    
    while (bytes_written < size) {
        int block_index = (offset + bytes_written) / BLOCK_SIZE;
        int block_offset = (offset + bytes_written) % BLOCK_SIZE;
        
        char block_buffer[BLOCK_SIZE];
        
        // 读取现有块数据（如果存在）
        if (read_data_block(inode_num, block_index, block_buffer) != 0) {
            break;
        }
        
        // 计算本次写入的字节数
        size_t bytes_to_write = min(BLOCK_SIZE - block_offset, size - bytes_written);
        
        // 写入数据到块缓冲区
        memcpy(block_buffer + block_offset, buffer + bytes_written, bytes_to_write);
        
        // 写回数据块（这会自动分配块如果需要的话）
        if (write_data_block(inode_num, block_index, block_buffer) != 0) {
            break;
        }
        
        bytes_written += bytes_to_write;
    }
    
    // 重新读取inode以获取可能在write_data_block中更新的字段
    read_inode(inode_num, &inode);
    
    // 更新文件大小和时间
    if (offset + bytes_written > inode.size) {
        inode.size = offset + bytes_written;
    }
    
    struct timespec current_time;
    clock_gettime(CLOCK_REALTIME, &current_time);
    inode.mtime = current_time.tv_sec;
    inode.ctime = current_time.tv_sec;
    inode.atime = current_time.tv_sec;
    inode.atime_nsec = current_time.tv_nsec;
    inode.mtime_nsec = current_time.tv_nsec;
    inode.ctime_nsec = current_time.tv_nsec;
    
    // 写回inode
    write_inode(inode_num, &inode);
    
    return bytes_written;
}

// 修改一个文件的大小（即分配或释放数据块）
//
// 错误处理：
// 1. 文件不存在时返回 -ENOENT
// 2. 没有足够的空间时返回 -ENOSPC
// 3. 超过单文件大小限制时返回 -EFBIG
//
// 参考实现：
// 注意分别处理增大和减小的情况
// 1. 计算需要的数据块数
// 2. 分配或释放数据块（以及 inode 中的记录）
// 3. 修改 inode 的 ctime
int fs_truncate(const char* path, off_t size) {
    fs_info("fs_truncate is called:%s\tsize:%ld\n", path, size);

    // 查找文件
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是文件
    if (!S_ISREG(inode.mode)) {
        return -EISDIR;
    }
    
    // 检查是否超过单文件大小限制
    int max_blocks = DIRECT_POINTER_COUNT + INDIRECT_POINTER_COUNT * (BLOCK_SIZE / sizeof(int));
    if (size > max_blocks * BLOCK_SIZE) {
        return -EFBIG;
    }
    
    // 计算当前需要的块数和新需要的块数
    int old_blocks_needed = (inode.size + BLOCK_SIZE - 1) / BLOCK_SIZE;
    int new_blocks_needed = (size + BLOCK_SIZE - 1) / BLOCK_SIZE;
    
    if (new_blocks_needed > old_blocks_needed) {
        // 文件增大，需要分配新块
        for (int i = old_blocks_needed; i < new_blocks_needed && i < DIRECT_POINTER_COUNT; i++) {
            if (inode.directPointers[i] == -1) {
                int new_block = allocate_data_block();
                if (new_block == -1) {
                    return -ENOSPC;
                }
                inode.directPointers[i] = new_block;
                
                // 初始化新块为零
                char zero_buffer[BLOCK_SIZE];
                memset(zero_buffer, 0, BLOCK_SIZE);
                disk_write(DATA_BLOCK_START + new_block, zero_buffer);
            }
        }
        inode.blockCount = new_blocks_needed;
    } else if (new_blocks_needed < old_blocks_needed) {
        // 文件缩小，需要释放多余的块
        for (int i = new_blocks_needed; i < old_blocks_needed && i < DIRECT_POINTER_COUNT; i++) {
            if (inode.directPointers[i] != -1) {
                free_data_block(inode.directPointers[i]);
                inode.directPointers[i] = -1;
            }
        }
        inode.blockCount = new_blocks_needed;
    }
    
    // 如果文件缩小且新大小在现有块的中间，需要清零部分内容
    if (size < inode.size && new_blocks_needed > 0) {
        int last_block_index = new_blocks_needed - 1;
        int offset_in_last_block = size % BLOCK_SIZE;
        
        if (offset_in_last_block > 0 && inode.directPointers[last_block_index] != -1) {
            char block_buffer[BLOCK_SIZE];
            if (disk_read(DATA_BLOCK_START + inode.directPointers[last_block_index], block_buffer) == 0) {
                // 清零从offset_in_last_block到块末尾的部分
                memset(block_buffer + offset_in_last_block, 0, BLOCK_SIZE - offset_in_last_block);
                disk_write(DATA_BLOCK_START + inode.directPointers[last_block_index], block_buffer);
            }
        }
    }
    
    // 更新文件大小和时间
    inode.size = size;
    struct timespec current_time;
    clock_gettime(CLOCK_REALTIME, &current_time);
    inode.mtime = current_time.tv_sec;
    inode.ctime = current_time.tv_sec;
    inode.atime = current_time.tv_sec;
    inode.atime_nsec = current_time.tv_nsec;
    inode.mtime_nsec = current_time.tv_nsec;
    inode.ctime_nsec = current_time.tv_nsec;
    
    // 写回inode
    return write_inode(inode_num, &inode);
}

// 修改条目的 atime 和 mtime
//
// 参考实现：
// 1. 通过 path 找到 inode
// 2. 根据传入的 tv 参数（分别是 atime 和 mtime）修改 inode 的 atime 和 mtime
// 3. 更新 inode 的 ctime（因为 utimens 本身修改了元数据）
int fs_utimens(const char* path, const struct timespec tv[2]) {
    fs_info("fs_utimens is called:%s\n", path);

    // 查找文件或目录
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    struct timespec current_time;
    clock_gettime(CLOCK_REALTIME, &current_time);
    
    // 更新atime
    if (tv && tv[0].tv_nsec != UTIME_OMIT) {
        if (tv[0].tv_nsec == UTIME_NOW) {
            inode.atime = current_time.tv_sec;
            inode.atime_nsec = current_time.tv_nsec;
        } else {
            inode.atime = tv[0].tv_sec;
            inode.atime_nsec = tv[0].tv_nsec;
        }
    }
    
    // 更新mtime  
    if (tv && tv[1].tv_nsec != UTIME_OMIT) {
        if (tv[1].tv_nsec == UTIME_NOW) {
            inode.mtime = current_time.tv_sec;
            inode.mtime_nsec = current_time.tv_nsec;
        } else {
            inode.mtime = tv[1].tv_sec;
            inode.mtime_nsec = tv[1].tv_nsec;
        }
    }
    
    // 更新ctime（因为元数据被修改了）
    inode.ctime = current_time.tv_sec;
    inode.ctime_nsec = current_time.tv_nsec;
    
    // 写回inode
    return write_inode(inode_num, &inode);
}

// 获取文件系统的状态
//
// 根据自己的文件系统填写即可，实现这个函数是可选的
//
// `df mnt` 和 `df -i mnt` 会触发这个函数
int fs_statfs(const char* path, struct statvfs* stat) {
    fs_info("fs_statfs is called:%s\n", path);

    // 填写文件系统统计信息
    stat->f_bsize = BLOCK_SIZE;                    // 文件系统块大小
    stat->f_frsize = BLOCK_SIZE;                   // 最小分配单元大小
    stat->f_blocks = g_superblock.blockCount;      // 总块数
    stat->f_bfree = g_superblock.freeBlockCount;   // 空闲块数
    stat->f_bavail = g_superblock.freeBlockCount;  // 用户可用的空闲块数
    stat->f_files = g_superblock.inodeCount;       // 总inode数
    stat->f_ffree = g_superblock.freeInodeCount;   // 空闲inode数
    stat->f_favail = g_superblock.freeInodeCount;  // 用户可用的空闲inode数
    stat->f_namemax = MAX_FILENAME_LEN;            // 文件名最大长度
    stat->f_fsid = 0x12345678;                     // 文件系统ID（使用魔数）
    stat->f_flag = 0;                              // 挂载标志

    return 0;
}

// 会在打开一个文件时被调用，完整的细节见 README.md
//
// 参考实现：
// 不考虑 `fs->fh` 时，这个函数事实上可以什么都不干
int fs_open(const char* path, struct fuse_file_info* fi) {
    fs_info("fs_open is called:%s\tflag:%o\n", path, fi->flags);

    // 查找文件
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是文件（不是目录）
    if (!S_ISREG(inode.mode)) {
        return -EISDIR;
    }
    
    // 可以在fi->fh中存储inode号，用于后续操作
    // fi->fh = inode_num;
    
    return 0;
}

// 会在一个文件被关闭时被调用，你可以在这里做相对于 `fs_open` 的一些清理工作
int fs_release(const char* path, struct fuse_file_info* fi) {
    fs_info("fs_release is called:%s\n", path);

    // 在简单的文件系统中，通常不需要特殊的清理工作
    // 如果使用了fi->fh存储文件句柄，可以在这里清理
    // fi->fh = 0;
    
    return 0;
}

// 类似于 `fs_open`，本实验中可以不做任何处理
int fs_opendir(const char* path, struct fuse_file_info* fi) {
    fs_info("fs_opendir is called:%s\n", path);

    // 查找目录
    int inode_num = find_inode_by_path(path);
    if (inode_num == -1) {
        return -ENOENT;
    }
    
    // 读取inode
    INode inode;
    if (read_inode(inode_num, &inode) != 0) {
        return -ENOENT;
    }
    
    // 检查是否是目录
    if (!S_ISDIR(inode.mode)) {
        return -ENOTDIR;
    }
    
    // 可以在fi->fh中存储inode号，用于后续操作
    // fi->fh = inode_num;
    
    return 0;
}

// 类似于 `fs_release`，本实验中可以不做任何处理
int fs_releasedir(const char* path, struct fuse_file_info* fi) {
    fs_info("fs_releasedir is called:%s\n", path);

    // 在简单的文件系统中，通常不需要特殊的清理工作
    // 如果使用了fi->fh存储目录句柄，可以在这里清理
    // fi->fh = 0;
    
    return 0;
}

static struct fuse_operations fs_operations = {.getattr = fs_getattr,
                                               .readdir = fs_readdir,
                                               .read = fs_read,
                                               .mkdir = fs_mkdir,
                                               .rmdir = fs_rmdir,
                                               .unlink = fs_unlink,
                                               .rename = fs_rename,
                                               .truncate = fs_truncate,
                                               .utimens = fs_utimens,
                                               .mknod = fs_mknod,
                                               .write = fs_write,
                                               .statfs = fs_statfs,
                                               .open = fs_open,
                                               .release = fs_release,
                                               .opendir = fs_opendir,
                                               .releasedir = fs_releasedir};

int main(int argc, char* argv[]) {
    // 理论上，你不需要也不应该修改 main 函数内的代码，只需要实现对应的函数

    int init_flag = !has_noinit_flag(&argc, argv);
    // 通过 make mount 或者 make debug 启动时，该值为 1
    // 通过 make mount_noinit 或者 make debug_noinit 启动时，该值为 0

    if (disk_mount(init_flag)) {  // 不需要修改
        fs_error("disk_mount failed!\n");
        return -1;
    }

    if (fs_mount(init_flag)) {  // 该函数用于初始化文件系统，实现细节见函数定义
        fs_error("fs_mount failed!\n");
        return -2;
    }

    int fuse_status = fuse_main(argc, argv, &fs_operations, NULL);
    // Ctrl+C 或者 make umount（fusermount） 时，fuse_main
    // 会退出到这里而不是整个程序退出

    // 如果你有一些工作要在文件系统被完全关闭前完成，比如确保所有数据都被写入磁盘，请在
    // fs_finalize 函数中完成
    return fs_finalize(fuse_status);
}
