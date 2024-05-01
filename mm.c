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
#define MAX_SAG 20

#define MAX(x, y)   ((x) > (y)? (x) : (y))

/* 크기와 할당비트를 워드로 packing*/
#define PACK(size, alloc)   ((size) | (alloc))

/* 포인터p가 참조하는 메모리의 값 read/ write */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* p가 가리키는 메모리에서 size와 할당비트를 read */
#define GET_SIZE(p)     (GET(p) & ~0x7) // 주소 p에 있는 헤더에서 size를 리턴
#define GET_ALLOC(p)    (GET(p) & 0x1) // 주소 p에 있는 헤더에서 할당비트를 리턴

/* 블록포인터의 header와 footer를 리턴 */
#define HEADER(bp)      ((char *)bp - WSIZE) // 블록포인터 bp에 워드 크기많금 빼서 head를 리턴
#define FOOTER(bp)      ((char *)bp + GET_SIZE(HEADER(bp)) - DSIZE) // 블록포인터 bp의 헤더를 통해 블록size만큼 이동후 더블워트만큼 빼서 footer를 리턴

/* 현재 블록의 이전블록과 다음 블록을 리턴 */
#define NEXT_BLOCK(bp)  ((char *)(bp) + GET_SIZE(HEADER(bp))) // 블록 포인터 bp에서 워드사이즈를 뺴면 헤더가 나오고 해더를 통해 블록의 사이즈만큼 이동
#define PREV_BLOCK(bp)  ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) // 블록 포인터 bp에서 더블워드 사이즈를 빼면 footer가 나오고 footer를 통해 이전 블록 사이즈만큼 이동
#define FIND_NEXT_FREE(bp) (*(void **)(bp + WSIZE))
#define FIND_PREV_FREE(bp) (*(void **)(bp))


/* 가용블록 리스트의 블록을 가리키는 포인터변수 */
static char *heap_listp;
static char *free_listp[MAX_SAG];

static void remove_free_list(void *bp){
    // printf("remove_free_list\n");
    if(bp == NULL)
        return;
    
    size_t size = GET_SIZE(HEADER(bp));
    size_t idx = 0;

    while ((idx < MAX_SAG-1) && (size > 1))
    {
        size >>= 1;
        idx++;
    }

    /* 
     * bp의 prev와 next가 없는경우 -> 헤더가 bp이고 bp밖에 존재하지 않는다
     * 헤더를 NULL로 만들고 리턴
     */ 
    if (FIND_PREV_FREE(bp) == NULL && FIND_NEXT_FREE(bp) == NULL){
        free_listp[idx] = NULL;
        return;
    }
    /*
     * bp의 next가 없는경우 -> bp가 맨 끝에 존재한다
     * bp prev의 FIND_NEXT_FREE를 NULL로 만든다
     */
    if(FIND_PREV_FREE(bp) != NULL && FIND_NEXT_FREE(bp) == NULL){
        FIND_NEXT_FREE(FIND_PREV_FREE(bp)) = NULL;
        return;
    }
    /* 
     * bp의 prev가 없는경우 -> 헤더가 bp이고 bp말고도 다른 경우가 있음
     * 헤더를 bp의 FIND_NEXT_FREE를 가리키게 만든다
     */
    if(FIND_PREV_FREE(bp) == NULL && FIND_NEXT_FREE(bp) != NULL){
        FIND_PREV_FREE(FIND_NEXT_FREE(bp)) = NULL;
        free_listp[idx] = FIND_NEXT_FREE(bp);
        return;
    }
    /*
     * bp의 양옆에 free블록이 존재하는경우 -> bp가 리스트 중간에 위치
     * bp의 FIND_PREV_FREE의 FIND_NEXT_FREE를 bp의 FIND_NEXT_FREE를 가리키게 하고
     * bp의 FIND_NEXT_FREE의 FIND_PREV_FREE를 bp의 FIND_PREV_FREE를 가리키게 한다
     */

    FIND_PREV_FREE(FIND_NEXT_FREE(bp)) = FIND_PREV_FREE(bp);
    FIND_NEXT_FREE(FIND_PREV_FREE(bp)) = FIND_NEXT_FREE(bp);

    return;
}

static void add_free_list(void *bp){
    // printf("add_free_list\n");
    if(bp == NULL)
        return;
    
    size_t size = GET_SIZE(HEADER(bp));
    size_t idx = 0;

    while (idx < (MAX_SAG-1) && size > 1)
    {
        size >>= 1;
        idx++;
    }
    size = GET_SIZE(HEADER(bp));

    void *cur = free_listp[idx];
    void *pre = NULL;

    while (cur != NULL && size > GET_SIZE(HEADER(cur)))
    {
        pre = cur;
        cur = FIND_NEXT_FREE(cur);
    }
    /*
     * 헤더가 아무도 안가리키는 경우
     * 헤더기 bp를 가리키게 만든다
     */
    if(cur == NULL && pre == NULL){
        FIND_NEXT_FREE(bp) = NULL;
        FIND_PREV_FREE(bp) = NULL;
        free_listp[idx] = bp;
        return;
    }
    /*
     * 맨 끝인경우
     * pre 앞에 bp를 붙인다
     */
    if (cur == NULL && pre != NULL){
        FIND_NEXT_FREE(pre) = bp;
        FIND_PREV_FREE(bp) = pre;
        FIND_NEXT_FREE(bp) = NULL;
        return ;
    }
    /*
     * cur이 헤더인 경우
     */
    if( cur != NULL && pre == NULL){
        FIND_NEXT_FREE(bp) = cur;
        FIND_PREV_FREE(cur) = bp;
        FIND_PREV_FREE(bp) = NULL;
        free_listp[idx] = bp;
        return;
    }
    /*
     * 중간인 경우
     * cur과 pre의 주소가 존재하는경우
     * pre의 next_free가 bp를 가리키게 하고 bp의 prev_free를 pre를 가리키게 한다
     * next의 prev_free가 bp를 가리키게 하고 bp의 next_free를 cur을 가리키게 한다
     */
    FIND_NEXT_FREE(pre) = bp;
    FIND_PREV_FREE(bp) = pre;
    FIND_PREV_FREE(cur) = bp;
    FIND_NEXT_FREE(bp) = cur;

    return;
}

static void *coalesce(void *bp)
{
    // printf("코알라\n");
    size_t prev_alloc = GET_ALLOC(FOOTER(PREV_BLOCK(bp)));
    size_t next_alloc = GET_ALLOC(HEADER(NEXT_BLOCK(bp)));
    size_t size = GET_SIZE(HEADER(bp));
    // printf("pre:%d next:%d size:%d\n",prev_alloc,next_alloc,size);
    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        remove_free_list(bp);
        remove_free_list(NEXT_BLOCK(bp));
        size += GET_SIZE(HEADER(NEXT_BLOCK(bp)));
        PUT(HEADER(bp), PACK(size, 0));
        PUT(FOOTER(bp), PACK(size, 0));
    }
    
    else if (!prev_alloc && next_alloc) {
        remove_free_list(bp);
        remove_free_list(PREV_BLOCK(bp));
        size += GET_SIZE(HEADER(PREV_BLOCK(bp)));
        PUT(FOOTER(bp), PACK(size, 0));
        PUT(HEADER(PREV_BLOCK(bp)), PACK(size, 0));
        bp = PREV_BLOCK(bp);
    }
    else{
        remove_free_list(bp);
        remove_free_list(PREV_BLOCK(bp));
        remove_free_list(NEXT_BLOCK(bp));
        size += GET_SIZE(HEADER(PREV_BLOCK(bp))) + GET_SIZE(FOOTER(NEXT_BLOCK(bp)));
        PUT(HEADER(PREV_BLOCK(bp)), PACK(size, 0));
        PUT(FOOTER(NEXT_BLOCK(bp)), PACK(size, 0));
        bp = PREV_BLOCK(bp);
    }
    add_free_list(bp);
    return bp;
}

static void *extend_heap(size_t words)
{
    // printf("extend_heap %d\n",words);
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HEADER(bp), PACK(size, 0));
    PUT(FOOTER(bp), PACK(size, 0));
    PUT(HEADER(NEXT_BLOCK(bp)), PACK(0, 1));
    
    add_free_list(bp);
    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    if(asize <= 0)
        return NULL;
    size_t searchsize = asize;
    size_t idx = 0;
    void *bp;

    while (idx < MAX_SAG)
    {
        if((idx == MAX_SAG-1) || ((searchsize <= 1) && (free_listp[idx] != NULL))){
            bp = free_listp[idx];

            while ((bp != NULL) && (asize > GET_SIZE(HEADER(bp)))){
                bp = FIND_NEXT_FREE(bp);
            }

            if( bp != NULL)
                return bp;
        }

        searchsize >>= 1;
        idx++;
    }
    
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HEADER(bp));

    remove_free_list(bp);
    if ((csize - asize) >= (2 * DSIZE)){
        PUT(HEADER(bp), PACK(asize, 1));
        PUT(FOOTER(bp), PACK(asize, 1));
        bp = NEXT_BLOCK(bp);
        PUT(HEADER(bp), PACK(csize - asize, 0));
        PUT(FOOTER(bp), PACK(csize - asize, 0));
        add_free_list(bp);
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
    
    for(int i = 0; i < MAX_SAG; i++){
        free_listp[i] = NULL;
    }
    
    PUT(heap_listp, 0); // 패딩 블록 설정
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 블록 헤더 설정
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 블록 풋터 설정
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 블록 헤더 설정
    heap_listp += (2 * DSIZE);

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
    // printf("malloc %d\n",size);
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
    // printf("free %d\n",GET_SIZE(HEADER(ptr)));
    size_t size = GET_SIZE(HEADER(ptr));

    PUT(HEADER(ptr), PACK(size, 0));
    PUT(FOOTER(ptr), PACK(size, 0));
    add_free_list(ptr);
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // printf("realloc\n");
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