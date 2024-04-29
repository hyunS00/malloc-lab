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
    "team 5",
    /* First member's full name */
    "kim hyunsoo",
    /* First member's email address */
    "tmp@email.com",
    /* Second member's full name (leave blank if none) */
    "bearN SOO",
    /* Second member's email address (leave blank if none) */
    "tmp@email.com"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + ALIGNMENT + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE   4 // 워드 크기를 정의
#define DSIZE   8 // 더블 워드 크기를 정의
#define CHUNKSIZE   (1<<12) // 청크 사이즈를 정의 청크사이즈는 힙을 할당할때 사용

#define MAX(x, y)   ((x) > (y)? (x) : (y))

/* 크기와 할당비트를 워드로 packing*/
#define PACK(size, alloc)   ((size) | (alloc))

/* 포인터p가 참조하는 메모리의 값 read/ write */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* p가 가리키는 메모리에서 size와 할당비트를 read */
#define GET_SIZE(p)     (GET(p) & ~0x7) // 주소 p에 있는 헤더에서 size를 리턴
#define GET_ALLOC(p)    (GET(p) & 0x1) // 주소 p에 있는 헤더에서 할당비트를 리턴
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2);
/* 블록포인터의 header와 footer를 리턴 */
#define HEADER(bp)      ((char *)bp - WSIZE) // 블록포인터 bp에 워드 크기많금 빼서 head를 리턴
#define FOOTER(bp)      ((char *)bp + GET_SIZE(HEADER(bp)) - DSIZE) // 블록포인터 bp의 헤더를 통해 블록size만큼 이동후 더블워트만큼 빼서 footer를 리턴

/* 현재 블록의 이전블록과 다음 블록을 리턴 */
#define NEXT_BLOCK(bp)  ((char *)(bp) + GET_SIZE(HEADER(bp))) // 블록 포인터 bp에서 워드사이즈를 뺴면 헤더가 나오고 해더를 통해 블록의 사이즈만큼 이동
#define PREV_BLOCK(bp)  ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) // 블록 포인터 bp에서 더블워드 사이즈를 빼면 footer가 나오고 footer를 통해 이전 블록 사이즈만큼 이동

/* 가용블록 리스트의 블록을 가리키는 포인터변수 */
static char *heap_listp;

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FOOTER(PREV_BLOCK(bp)));
    size_t next_alloc = GET_ALLOC(HEADER(NEXT_BLOCK(bp)));
    size_t size = GET_SIZE(HEADER(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HEADER(NEXT_BLOCK(bp)));
        PUT(HEADER(bp), PACK(size, 0));
        PUT(FOOTER(bp), PACK(size, 0));
    }
    
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HEADER(PREV_BLOCK(bp)));
        PUT(FOOTER(bp), PACK(size, 0));
        PUT(HEADER(PREV_BLOCK(bp)), PACK(size, 0));
        bp = PREV_BLOCK(bp);
    }

    else{
        size += GET_SIZE(HEADER(PREV_BLOCK(bp))) + GET_SIZE(FOOTER(NEXT_BLOCK(bp)));
        PUT(HEADER(PREV_BLOCK(bp)), PACK(size, 0));
        PUT(FOOTER(NEXT_BLOCK(bp)), PACK(size, 0));
        bp = PREV_BLOCK(bp);
    }
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HEADER(bp), PACK(size, 0));
    PUT(FOOTER(bp), PACK(size, 0));
    PUT(HEADER(NEXT_BLOCK(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    if(asize <= 0)
        return NULL;
    
    void *bp = heap_listp;
    while (GET_SIZE(HEADER(bp)) > 0)
    {
        if(!GET_ALLOC(HEADER(bp)) && (asize <= GET_SIZE(HEADER(bp)))){
            return bp;
        }
        bp = NEXT_BLOCK(bp);
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HEADER(bp));

    if ((csize - asize) >= (2 * DSIZE)){
        PUT(HEADER(bp), PACK(asize, 1));
        PUT(FOOTER(bp), PACK(asize, 1));
        bp = NEXT_BLOCK(bp);
        PUT(HEADER(bp), PACK(csize - asize, 0));
        PUT(FOOTER(bp), PACK(csize - asize, 0));
    }
    else{
        PUT(HEADER(bp), PACK(csize, 1));
        PUT(FOOTER(bp), PACK(csize, 1));
    }
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)
        return -1;
    
    PUT(heap_listp, 0); // 패딩 블록 설정
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 블록 헤더 설정
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 블록 풋터 설정
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 블록 헤더 설정
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = ALIGN(size);

    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HEADER(ptr));

    PUT(HEADER(ptr), PACK(size, 1));
    PUT(FOOTER(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HEADER(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}