module MergeSort

%default total

data Zippable : List a -> List a -> Type where
    ZipNil : Zippable Nil Nil
    ZipCons : Zippable l r -> Zippable (x :: r) l

flatZip : List a -> List a -> List a
flatZip Nil r = r
flatZip l Nil = l
flatZip (x :: xs) (y :: ys) = x :: y :: flatZip xs ys

flatZipConsOne : flatZip (x :: r) l = x :: flatZip l r
flatZipConsOne {l=Nil} = Refl
flatZipConsOne {l=x::xs} {r=Nil} = Refl
flatZipConsOne {x} {l=y::ys} {r=z::zs} = cong {f=\l=>x::y::l} flatZipConsOne

flatZipNilRightNeutral : l = flatZip l []
flatZipNilRightNeutral {l=Nil} = Refl
flatZipNilRightNeutral {l=x::xs} = Refl

data Split : (a : Type) -> List a -> Type where
    SplitNil : Split a []
    SplitSingleton : (x : a) -> Split a [x]
    SplitInTwo :
        Split a l ->
        Split a r ->
        Zippable l r ->
        Split a (flatZip l r)

split : (l : List a) -> Split a l
split [] = SplitNil
split (z :: zs) = insert z (split zs) where
    insert : (x : a) -> Split a xs -> Split a (x :: xs)
    insert x SplitNil = SplitSingleton x
    insert x (SplitSingleton y) =
        SplitInTwo (SplitSingleton x) (SplitSingleton y)
            (ZipCons (ZipCons ZipNil))
    insert x (SplitInTwo sl sr ziplr) =
        (replace flatZipConsOne (SplitInTwo (insert x sr) sl (ZipCons ziplr)))

data WeakPerm : List a -> List a -> Type where
    WPRefl : WeakPerm l l
    WPLeftSmaller :
        WeakPerm (x :: xs) l ->
        WeakPerm (x :: flatZip xs r) (flatZip l r)
    WPRightSmaller :
        WeakPerm (x :: xs) r ->
        WeakPerm (x :: flatZip l xs) (flatZip l r)

notLTEtoGTE : Not (LTE x y) -> LTE y x
notLTEtoGTE {y=Z} _ = LTEZero
notLTEtoGTE {x=Z} notxLTEy = absurd (notxLTEy LTEZero)
notLTEtoGTE {x=S j} {y=S k} notxLTEy =
    LTESucc (notLTEtoGTE (notxLTEy . LTESucc))

data LTEAll : (x : Nat) -> List Nat -> Type where
    LTENil : LTEAll x []
    LTECons : LTE x y -> LTEAll x ys -> LTEAll x (y :: ys)

lteAllTrans : LTE x y -> LTEAll y ys -> LTEAll x ys
lteAllTrans _ LTENil = LTENil
lteAllTrans xLTEy (LTECons yLTEz yLTEzs) =
    LTECons (lteTransitive xLTEy yLTEz) (lteAllTrans xLTEy yLTEzs)

lteAllPlusOne : LTE x y -> LTEAll y ys -> LTEAll x (y :: ys)
lteAllPlusOne xLTEy LTENil = LTECons xLTEy LTENil
lteAllPlusOne xLTEy (LTECons yLTEz yLTEzs) =
    LTECons
        xLTEy
        (LTECons (lteTransitive xLTEy yLTEz) (lteAllTrans xLTEy yLTEzs))

lteAllFromFlatZip : LTEAll x (flatZip l r) -> (LTEAll x l, LTEAll x r)
lteAllFromFlatZip {l=Nil} p = (LTENil, p)
lteAllFromFlatZip {r=Nil} p = (replace (sym flatZipNilRightNeutral) p, LTENil)
lteAllFromFlatZip {x} {l=y::ys} {r=z::zs} (LTECons xLTEy (LTECons xLTEz p)) =
    let
        (xLTEys, xLTEzs) = lteAllFromFlatZip p
    in
        (LTECons xLTEy xLTEys, LTECons xLTEz xLTEzs)

lteAllToFlatZip: LTEAll x l -> LTEAll x r -> LTEAll x (flatZip l r)
lteAllToFlatZip LTENil lr = lr
lteAllToFlatZip sl LTENil = replace flatZipNilRightNeutral sl
lteAllToFlatZip (LTECons xLTEy xLTEys) (LTECons xLTEz xLTEzs) =
    LTECons xLTEy (LTECons xLTEz (lteAllToFlatZip xLTEys xLTEzs))

lteAllPermInvariant : WeakPerm l r -> LTEAll x l -> LTEAll x r
lteAllPermInvariant WPRefl x = x
lteAllPermInvariant (WPLeftSmaller p) (LTECons xLTEy xLTEfzxsr) =
    let
        (xLTExs, xLTEr) = lteAllFromFlatZip xLTEfzxsr
    in
        lteAllToFlatZip (lteAllPermInvariant p (LTECons xLTEy xLTExs)) xLTEr
lteAllPermInvariant (WPRightSmaller p) (LTECons xLTEy xLTEfzlxs) =
    let
        (xLTEl, xLTExs) = lteAllFromFlatZip xLTEfzlxs
    in
        lteAllToFlatZip xLTEl (lteAllPermInvariant p (LTECons xLTEy xLTExs))

data Sort : List Nat-> Type where
    SortNil : Sort []
    SortCons :
        (x : Nat) ->
        (Sort l) ->
        LTEAll x l ->
        WeakPerm (x :: l) xl ->
        Sort xl

toList : Sort l -> List Nat
toList SortNil = []
toList (SortCons x xs _ _) = x :: toList xs

merge : Sort l -> Sort r -> Sort (flatZip l r)
merge SortNil sr = sr
merge sl SortNil = replace flatZipNilRightNeutral sl
merge (SortCons x xs xLTExs lEQxxs) (SortCons y ys yLTEys rEQyys)
    with (isLTE x y)
        | Yes xLTEy = SortCons x (merge xs (SortCons y ys yLTEys rEQyys))
            (lteAllToFlatZip
                xLTExs
                (lteAllPermInvariant rEQyys (lteAllPlusOne xLTEy yLTEys)))
            (WPLeftSmaller lEQxxs)
        | No xNLTEy = SortCons y (merge (SortCons x xs xLTExs lEQxxs) ys)
            (lteAllToFlatZip
                (lteAllPermInvariant
                    lEQxxs
                    (lteAllPlusOne (notLTEtoGTE xNLTEy) xLTExs))
                yLTEys)
            (WPRightSmaller rEQyys)

verifiedMergeSort : Split Nat l -> Sort l
verifiedMergeSort SplitNil = SortNil
verifiedMergeSort (SplitSingleton x) = SortCons x SortNil LTENil WPRefl
verifiedMergeSort (SplitInTwo sl sr _) =
    merge (verifiedMergeSort sl) (verifiedMergeSort sr)

mergeSort : List Nat -> List Nat
mergeSort l = toList (verifiedMergeSort (split l))
