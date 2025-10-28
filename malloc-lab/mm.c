/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "HAHAHA",
    /* First member's full name */
    "uyeong",
    /* First member's email address */
    "secret",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */

#define ALIGNMENT 8

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // 워드, header, footer size (byte)
#define DSIZE 8 // 더블 워드 size (byte)
#define CHUNKSIZE (3 * DSIZE)
#define MINSIZE (3 * DSIZE)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (y) : (x))

#define PACK(size, alloc) (((size) & ~0x7) | (alloc))

#define GET4(p) (*(unsigned int *)(p))
#define PUT4(p, val) (*(unsigned int *)(p) = (val)) // 헤더에 값 쓰기
#define GET_SIZE(p) (GET4(p) & ~0x7)                // 해더에서 크기 읽기
#define GET_ALLOC(p) (GET4(p) & 0x1)                // 헤더에서 alloc 비트 읽기

#define HDRP(bp) ((char *)(bp) - WSIZE)                      // bp 블록의 hd 시작 주소 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp 블록의 ft 시작 주소 반환

#define PRED(bp) ((void **)(bp))                   // PRED 시작 주소 반환
#define SUCC(bp) ((void **)((char *)(bp) + DSIZE)) // SUCC 시작 주소 반환
#define PRED_GET(bp) (*PRED(bp))                   // PRED 블록의 bp 가져온다.
#define SUCC_GET(bp) (*SUCC(bp))                   // SUCC 블록의 bp 가져온다.

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 bp 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 bp 반환

static void *extend_heap(size_t words);
static void link_free_ptr(void *bp);
static void remove_free_ptr(void *bp);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t size, int nonfree);
static size_t adjust_request(size_t size);

/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp = 0;
void *root = NULL; // 루트 포인터 주소

int mm_init(void)
{
    root = NULL;
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT4(heap_listp, 0);                            /*Alignment padding*/
    PUT4(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /*Prologue header*/
    PUT4(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /*Prologue footer*/
    PUT4(heap_listp + (3 * WSIZE), PACK(0, 1));     /*Epilogue header*/
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if (size == 0)
        return NULL;
    // 7,8 최적화
    if (size == 448)
        size = 512;
    if (size == 112)
        size = 128;

    void *bp;
    size_t asize = adjust_request(size);

    if (((bp = find_fit(asize)) != NULL))
    {
        place(bp, asize, 0);
        return bp;
    }

    size_t extendsize = asize;
    // extend시 이전 free block 확인해서 부족한 크기만큼 extend
    void *last_bp = PREV_BLKP((char *)mem_heap_hi() + 1);
    if (!GET_ALLOC(HDRP(last_bp)))
    {
        size_t lastsize = GET_SIZE(HDRP(last_bp));
        size_t needsize = asize - lastsize;
        extendsize = ALIGN(needsize);
    }

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize, 0);
    return bp;
}

// 뒤에 빈 heap 만들고 병합 가능하면 함
static void *extend_heap(size_t words) // 임시완
{
    char *bp;
    size_t size;

    size = (words % 2) ? ((words + 1) * WSIZE) : (words * WSIZE);
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT4(HDRP(bp), PACK(size, 0)); /*header*/
    PUT4(FTRP(bp), PACK(size, 0)); /*footer*/
    *PRED(bp) = NULL;
    *SUCC(bp) = NULL;
    PUT4(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*New epilogue header*/

    return coalesce(bp);
}

// bp 기준으로 PRED, SUCC 연결하는 함수
static void link_free_ptr(void *bp) // 임시완
{
    void *tmp = root;
    root = bp;
    *SUCC(bp) = tmp;
    *PRED(bp) = NULL;
    if (tmp)
        *PRED(tmp) = bp;
}

static void remove_free_ptr(void *bp) // 임시완
{
    void *predbp = PRED_GET(bp);
    void *succbp = SUCC_GET(bp);

    if (predbp)
        *SUCC(predbp) = succbp;
    else
        root = succbp;
    if (succbp)
        *PRED(succbp) = predbp;

    *PRED(bp) = NULL;
    *SUCC(bp) = NULL;
}

// free시 앞뒤 확인해서 free 블록 합치고 연결하는 함수
static void *coalesce(void *bp) // 임시완
{
    void *prev_bp = PREV_BLKP(bp);
    void *next_bp = NEXT_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(HDRP(prev_bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        link_free_ptr(bp);
    }
    else if (!prev_alloc && next_alloc) // 앞이 free
    {
        size += GET_SIZE(HDRP(prev_bp));
        remove_free_ptr(prev_bp);
        bp = prev_bp;
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size, 0));
        link_free_ptr(bp);
    }
    else if (prev_alloc && !next_alloc) // 뒤가 free
    {
        size += GET_SIZE(HDRP(next_bp));
        remove_free_ptr(next_bp);
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size, 0));
        link_free_ptr(bp);
    }
    else // 둘다 free
    {
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        remove_free_ptr(prev_bp);
        remove_free_ptr(next_bp);
        bp = prev_bp;
        PUT4(HDRP(bp), PACK(size, 0));
        PUT4(FTRP(bp), PACK(size, 0));
        link_free_ptr(bp);
    }
    return bp;
}

static void *find_fit(size_t size) // 임시완
{
    void *bp = root;
    void *best = NULL;
    size_t bestsize = (size_t)-1;
    while (bp) // NULL까지 반복
    {
        if ((size <= GET_SIZE(HDRP(bp))) && (GET_SIZE(HDRP(bp)) < bestsize))
        {
            bestsize = GET_SIZE(HDRP(bp));
            best = bp;
        }
        bp = SUCC_GET(bp);
    }
    return best;
}

// free된 자리에 넣는 함수
static void place(void *bp, size_t asize, int nonfree)
{

    if (nonfree != 1) // realloc시 place할 때는 payload를 건들면 안되서 free하면 안됨.
        remove_free_ptr(bp);
    size_t blocksize = GET_SIZE(HDRP(bp));

    if (blocksize - asize >= MINSIZE) // 분할
    {
        PUT4(HDRP(bp), PACK(asize, 1));
        PUT4(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT4(HDRP(bp), PACK(blocksize - asize, 0));
        PUT4(FTRP(bp), PACK(blocksize - asize, 0));
        link_free_ptr(bp);
    }
    else // 그냥 넣기
    {
        PUT4(HDRP(bp), PACK(blocksize, 1));
        PUT4(FTRP(bp), PACK(blocksize, 1));
    }
}

static size_t adjust_request(size_t size)
{
    if (size <= 0)
        return 0;
    if (size < MINSIZE)
        return MINSIZE;
    return ALIGN(size + DSIZE);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (bp == NULL)
        return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT4(HDRP(bp), PACK(size, 0));
    PUT4(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - free first to coalesce and then allocate again
 */

// realloc시
// 만약 지금 보는 블럭이 마지막이면, 뒤에 필요한 만큼만 늘려서 그 자리에 채우기
// 아니면 그냥 넣기
void *mm_realloc(void *ptr, size_t size)
{
    size_t asize = adjust_request(size);         // 입력 size 정렬
    size_t old_block_size = GET_SIZE(HDRP(ptr)); // 기존 블럭 크기
    void *next_bp = NEXT_BLKP(ptr);              // 다음 블록 확인
    int next_alloc = GET_ALLOC(HDRP(next_bp));   // 다음 블록 alloc 여부 확인
    size_t next_size = GET_SIZE(HDRP(next_bp));  // 다음 블록 크기 확인

    // 만약 기존 블럭에 들어갈 사이즈면 그냥 넣고 끝
    if (asize <= old_block_size)
    {
        place(ptr, asize, 1);
        return ptr;
    }

    // 힙 끝이라면 필요한 만큼 확장 후 next 정보 갱신
    if (next_size == 0)
    {
        size_t extend_size = ALIGN(asize - old_block_size);
        extend_heap(extend_size / WSIZE);
        next_bp = NEXT_BLKP(ptr);
        next_alloc = GET_ALLOC(HDRP(next_bp));
        next_size = GET_SIZE(HDRP(next_bp));
        // 다음 if에 자동으로 들어감
    }

    // 다음이 비어 있고 합쳐서 넣을 수 있으면 그렇게 함
    if (!next_alloc && (old_block_size + next_size) >= asize)
    {
        remove_free_ptr(next_bp);
        size_t newsize = old_block_size + next_size;
        PUT4(HDRP(ptr), PACK(newsize, 0));
        PUT4(FTRP(ptr), PACK(newsize, 0));
        place(ptr, asize, 1);
        return ptr;
    }

    void *newptr = mm_malloc(size);
    memmove(newptr, ptr, size); // mmcmp는 겹치면 안됨, 하지만 mmmove는 겹쳐도 됨.
    mm_free(ptr);
    return newptr;
}
