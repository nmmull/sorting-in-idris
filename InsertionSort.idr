module InsertionSort

%default total
%access public export

data WeakPerm : List a -> List a -> Type where
    WPRefl : WeakPerm l l
    WPCons : WeakPerm l r -> WeakPerm (x :: l) (x :: r)
    WPFlip : WeakPerm (x :: y :: l) r -> WeakPerm (y :: x :: l) r

notLTEtoGTE : Not (LTE x y) -> LTE y x
notLTEtoGTE {y=Z} _ = LTEZero
notLTEtoGTE {x=Z} notxLTEy = absurd (notxLTEy LTEZero)
notLTEtoGTE {x=S j} {y=S k} notxLTEy =
    LTESucc (notLTEtoGTE (notxLTEy . LTESucc))

data LTEAll : (x : Nat) -> (l : List Nat) -> Type where
    LTENil : LTEAll x Nil
    LTECons : LTE x y -> LTEAll x ys -> LTEAll x (y :: ys)

lteMinToLTEAll : LTE x y -> LTEAll y l -> LTEAll x l
lteMinToLTEAll _ LTENil = LTENil
lteMinToLTEAll xLTEy (LTECons yLTEz yLTEzs) =
    LTECons (lteTransitive xLTEy yLTEz) (lteMinToLTEAll xLTEy yLTEzs)

lteAllPermInvariant : WeakPerm l r -> LTEAll x l-> LTEAll x r
lteAllPermInvariant WPRefl xLTEl = xLTEl
lteAllPermInvariant (WPCons prf) (LTECons xLTEy xLTEys) =
    LTECons xLTEy (lteAllPermInvariant prf xLTEys)
lteAllPermInvariant (WPFlip WPRefl) (LTECons xLTEy (LTECons xLTEz xLTEl)) =
    LTECons xLTEz (LTECons xLTEy xLTEl)
lteAllPermInvariant (WPFlip (WPCons p)) (LTECons xLTEy (LTECons xLTEz xLTEl)) =
    LTECons xLTEz (lteAllPermInvariant p (LTECons xLTEy xLTEl))
lteAllPermInvariant (WPFlip (WPFlip p1)) p2 = lteAllPermInvariant p1 p2

data Sort : List Nat -> Type where
    SortNil : Sort Nil
    SortCons :
        (x : Nat) ->
        (xs : Sort l) ->
        LTEAll x l ->
        WeakPerm (x :: l) xl ->
        Sort xl

toList : Sort l -> List Nat
toList SortNil = Nil
toList (SortCons x xs _ _) = x :: toList xs

insert : (x : Nat) -> Sort l -> Sort (x :: l)
insert x SortNil = SortCons x SortNil LTENil WPRefl
insert x (SortCons y ys yLTEys ysPerm) with (isLTE x y)
    | Yes xLTEy = SortCons x (SortCons y ys yLTEys ysPerm)
        (lteAllPermInvariant
            ysPerm
            (LTECons xLTEy (lteMinToLTEAll xLTEy yLTEys)))
        WPRefl
    | No xNLTEy = SortCons y (insert x ys)
        (LTECons (notLTEtoGTE xNLTEy) yLTEys)
        (WPFlip (WPCons ysPerm))

verifiedInsertionSort : (l : List Nat) -> Sort l
verifiedInsertionSort Nil = SortNil
verifiedInsertionSort (x :: xs) = insert x (verifiedInsertionSort xs)

insertionSort : List Nat -> List Nat
insertionSort l = toList (verifiedInsertionSort l)
