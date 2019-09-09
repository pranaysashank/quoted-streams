{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types #-}

module StreamLib where

import Prelude hiding (concatMap, filter, map, zipWith, foldl)
import Language.Haskell.TH.Syntax

type Code a = Q (TExp a)

data Step s a
    = Nil
    | Cons a s

data Card = AtMost1 | Many
data Producer_Type a s =
    Unfold
        { card :: Card
        , step :: forall w. s -> (Step s a -> Code w) -> Code w
        }

data Producer a =
    forall s. Producer (Code s) (Producer_Type a (Code s))

data Stream_Type a
    = Linear (Producer a)
    | forall b. Nested (Producer (Code b)) ((Code b) -> Stream_Type a)

type Stream a = Stream_Type (Code a)

yield :: Code a -> Stream a
yield x =
    Linear
        (Producer [|| () ||] (Unfold AtMost1 (\_ k -> k (Cons x [|| () ||]))))

cons :: Code a -> Stream a -> Stream a
cons x (Linear (Producer init unf)) =
    let prod =
            Producer [|| Nothing ||] $
            Unfold
                Many
                (\s k ->
                     [|| case $$s of
                             Nothing -> $$(k $ Cons x [|| Just $$init ||])
                             Just s ->
                                 $$(step
                                        unf
                                        [|| s ||]
                                        (\ste ->
                                             case ste of
                                                 Nil -> k Nil
                                                 Cons a t ->
                                                     k (Cons a [|| Just $$t ||]))) ||])
     in Linear prod
cons x (Nested prod nestf) = Nested prod (\b -> cons x (nestf b))

concatMap :: (Code a -> Stream b) -> Stream a -> Stream b
concatMap tr st =
    case st of
        Linear prod -> Nested prod tr
        Nested prod nestf -> Nested prod (\a -> concatMap tr $ nestf a)

fromList :: Code [a] -> Stream a
fromList xs =
    let prod =
            Producer
                xs
                (Unfold
                     { card = Many
                     , step =
                           \s f ->
                               [|| case $$s of
                                       (x:xs) ->
                                           $$(f $
                                              Cons [|| x ||] [|| xs ||])
                                       [] -> $$(f Nil) ||]
                     })
     in Linear prod

map :: (Code a -> Code b) -> Stream a -> Stream b
map f (Linear (Producer init unf)) =
    let step' s k =
            step unf s $ \s ->
                case s of
                    Nil -> k Nil
                    Cons a t ->
                        [|| let a' = $$(f a)
                             in $$(k $ Cons [|| a' ||] t) ||]
     in Linear $ Producer init (Unfold (card unf) step')
map f (Nested prod nestf) = Nested prod (\b -> map f (nestf b))

foldl ::
       (Code b -> Code a -> Code b)
    -> Code b
    -> Stream a
    -> Code b
foldl f acc (Linear (Producer state unf)) = go state
  where
    go st =
        case card unf of
            AtMost1 ->
                [|| $$(step unf st $ \ste ->
                           case ste of
                               Nil -> acc
                               Cons a _ -> f acc a) ||]
            Many ->
                [|| let go' z s =
                            $$(step unf [|| s ||] $ \ste ->
                                   case ste of
                                       Nil -> [|| z ||]
                                       Cons a t ->
                                           [|| go' $$(f [|| z ||] a) $$t ||])
                     in go' $$acc $$st ||]
foldl f acc (Nested prod nestf) =
    foldl (\b p -> foldl f b (nestf p)) acc (Linear prod)

filter :: (Code a -> Code Bool) -> Stream a -> Stream a
filter f stream =
    let prod x =
            Producer
                (f x)
                (Unfold
                     { card = AtMost1
                     , step =
                           \s f ->
                               [|| if $$s
                                       then $$(f (Cons x [|| False ||]))
                                       else $$(f Nil) ||]
                     })
     in concatMap (\x -> Linear (prod x)) stream

enumFromNTo :: Code Int -> Code Int -> Stream Int
enumFromNTo n to =
    let prod =
            Producer
                n
                (Unfold
                     { card = Many
                     , step =
                           \s f ->
                               [|| if $$s <= $$to
                                       then $$(f (Cons s [|| ($$s + 1) ||]))
                                       else $$(f Nil) ||]
                     })
     in Linear prod


ftest :: Code (IO Int)
ftest =
    --foldl (\a b -> [|| $$a + $$b ||]) [|| 0 ||]
    foldl (\b a -> [|| $$b >>= \b' -> print b' >> $$a >>= \a' -> return (a' + b') ||]) [|| return 0 ||]
    $ map (\a -> [|| print ($$a + 1) >> return ($$a + 1) ||])
    $ filter (\a -> [|| $$a < 4 ||])
    $ concatMap (\x -> enumFromNTo x [|| 4 ||])
    $ fromList [|| [0, 1, 2, 3, 4] ||]

{-
data Card = AtMost1 | Many
data Producer_Type m a s =
    Unfold
        { card :: Card
        , step :: forall w. s -> (Step s a -> Code (m w)) -> Code (m w)
        }

data Producer m a =
    forall s. Producer (Code s) (Producer_Type m a (Code s))

data Stream_Type m a
    = Linear (Producer m a)
    | forall b. Nested (Producer m (Code b)) ((Code b) -> Stream_Type m a)

type Stream m a = Stream_Type m (Code a)

concatMapM :: (Code a -> Stream m b) -> Stream m a -> Stream m b
concatMapM tr st =
    case st of
        Linear prod -> Nested prod tr
        Nested prod nestf -> Nested prod (\a -> concatMapM tr $ nestf a)

concatMap :: (Code a -> Stream m b) -> Stream m a -> Stream m b
concatMap f = concatMapM f

fromList :: Code [a] -> Stream m a
fromList xs =
    let prod =
            Producer
                xs
                (Unfold
                     { card = Many
                     , step =
                           \s f ->
                               [|| case $$s of
                                       (x:xs) ->
                                           $$(f $
                                              Cons [|| x ||] [|| xs ||])
                                       [] -> $$(f Nil) ||]
                     })
     in Linear prod


foldlM ::
       (Code (m b) -> Code a -> Code (m b))
    -> Code (m b)
    -> Stream m a
    -> Code (m b)
foldlM f acc (Linear (Producer state unf)) = go state
  where
    go st =
        case card unf of
            AtMost1 ->
                [|| $$(step unf st $ \ste ->
                           case ste of
                               Nil -> [|| $$acc ||]
                               Cons a _ -> f acc a) ||]
            Many ->
                [|| let go' z s =
                            $$(step unf [|| s ||] $ \ste ->
                                   case ste of
                                       Nil -> [|| z ||]
                                       Cons a t ->
                                           [|| go' $$(f [|| z ||] a) $$t ||])
                     in go' $$acc $$st ||]
foldlM f acc (Nested prod nestf) =
    foldlM (\b p -> foldlM f b (nestf p)) acc (Linear prod)

foldl ::
       Monad m
    => (Code b -> Code a -> Code b)
    -> Code b
    -> Stream m a
    -> Code (m b)
foldl f z =
    foldlM
        (\b a -> [|| $$b >>= \b' -> return $$(f [|| b' ||] a) ||])
        [|| return $$z ||]

filter :: (Code a -> Code Bool) -> Stream m a -> Stream m a
filter f stream =
    let prod x =
            Producer
                (f x)
                (Unfold
                     { card = AtMost1
                     , step =
                           \s f ->
                               [|| if $$s
                                       then $$(f (Cons x [|| False ||]))
                                       else $$(f Nil) ||]
                     })
     in concatMap (\x -> Linear (prod x)) stream


enumFromNTo :: Code Int -> Code Int -> Stream m Int
enumFromNTo n to =
    let prod =
            Producer
                n
                (Unfold
                     { card = Many
                     , step =
                           \s f ->
                               [|| if $$s <= $$to
                                       then $$(f (Cons s [|| ($$s + 1) ||]))
                                       else $$(f Nil) ||]
                     })
     in Linear prod


ftest :: Code (IO Int)
ftest =
    --foldl (\a b -> [|| $$a + $$b ||]) [|| 0 ||]
    foldlM (\b a -> [|| $$b >>= \b' -> print b' >> return ($$a + b') ||]) [|| return 0 ||]
    $ fromList [|| [0, 1, 2, 3, 4] ||]
{-
    fold (\a b -> [|| $$a + $$b ||]) [|| 0 ||]
    $ filter (\a -> [|| $$a < 4 ||])
    $ concatMap (\x -> enumFromNTo x [|| 4 ||])
    $ fromList [|| [0, 1, 2, 3, 4] ||]
-}
-}

{-
{-
data Stream a = forall s. Stream s (s -> Step s a)

smap :: (a -> b) -> Stream a -> Stream b
smap = undefined
-}
data StStream a =
    forall s. StStream (Code s) (Code s -> Code (Step s a))

map :: (Code a -> Code b) -> StStream a -> StStream b
map f (StStream state stepa) = StStream state stepb
  where
    stepb st =
        [|| case $$(stepa st) of
                Nil -> Nil
                Cons a s -> Cons $$(f [|| a ||]) s ||]


fromList :: Code [a] -> StStream a
fromList c = StStream c step
  where
    step c =
        [|| case $$c of
               [] -> Nil
               (x:xs) -> Cons x xs ||]

fold :: (Code b -> Code a -> Code b) -> Code b -> StStream a -> Code b
fold f acc (StStream state step) = go acc state
  where
    go acc' st =
      [|| let go' st' z = case $$(step [|| st' ||]) of
                              Nil -> z
                              Cons a s -> go' s $$(f [|| z ||] [|| a ||])
          in go' $$st $$acc'
      ||]

uncons :: StStream a -> Code (Maybe a)
uncons (StStream state step) = go state
  where
    go st =
      [|| case $$(step st) of
              Nil -> Nothing
              Cons a _ -> Just a
      ||]

sgo :: (Code a -> StStream b) -> Code s -> (Code s -> Code (Step s a)) -> StStream b
sgo f state step = StStream [|| Left $$state ||] go
  where
    go state = [||
        let go' (Left st) = case $$(step [|| st ||]) of
              Nil -> Nil
              Cons a s -> go' (Left s) -- (Right (f [|| a ||], [|| s ||])))
          in go' $$state
      ||]

stconcatMap :: (Code a -> StStream b) -> StStream a -> StStream b
stconcatMap f (StStream state stepa) = sgo f state stepa{-StStream [|| Left $$state ||] stepb
  where
    stepb state = undefined-}
{-        [||  go' $$state
        ||]

    go' (Left st) =
                    case $$(stepa [|| st ||]) of
                        Nil -> Nil
                        Cons a s -> go' (Right (f [|| a ||], s))
    go' (Right (StStream inner_s inner_step, st)) =
                   case $$(inner_step inner_s) of
                        Nil -> go' (Left st)
                        Cons b s -> Cons b $ Right (StStream [|| s ||] inner_step, st)

    stepb state =
        [|| let go' (Left st) =
                    case $$(stepa [|| st ||]) of
                        Nil -> Nil
                        Cons a s -> go' (Right (f [|| a ||], s))
                go' (Right (StStream inner_s inner_step, st)) =
                    case $$(inner_step inner_s) of
                        Nil -> go' (Left st)
                        Cons b s -> Cons b $ Right (StStream [|| s ||] inner_step, st)
            in go' $$state
        ||]-}


enumFromNTo :: Code Int -> Code Int -> StStream Int
enumFromNTo n to = StStream n step
  where
    step n =
        [|| let go n = if n <= $$to
                       then Cons n (n+1)
                       else Nil
            in go $$n
        ||]

zipWith ::
       (Code a -> Code b -> Code c) -> StStream a -> StStream b -> StStream c
zipWith f (StStream statea stepa) (StStream stateb stepb) =
    StStream [|| ($$statea, $$stateb, Nothing) ||] stepc
  where
    stepc st = [|| let stepc' (sa, sb, Nothing) =
                           case $$(stepa [|| sa ||]) of
                               Nil -> Nil
                               Cons a sa' -> stepc' (sa', sb, Just a)
                       stepc' (sa, sb, Just a) =
                           case $$(stepb [|| sb ||]) of
                               Nil -> Nil
                               Cons b sb' -> Cons $$(f [|| a ||] [|| b ||]) (sa, sb', Nothing)
                   in stepc' $$st
               ||]

test :: Code Int
test = fold (\a b -> [|| $$a + $$b ||]) [|| 0 ||] $ map (\a -> [|| $$a * $$a ||]) $ fromList [|| [0,1,2,3,4] ||]

zipWithTest :: Code Int
zipWithTest =  fold (\a b -> [|| $$a + $$b ||]) [|| 0 ||]
               $ zipWith (\a b -> b)
                         (enumFromNTo [|| 1 ||] [|| 10 ||])
                         (enumFromNTo [|| 11 ||] [|| 20 ||])

{-
test' :: Code Int
test' = fold (\a b -> [|| $$a + $$b ||]) [|| 0 ||]
        $ stconcatMap (\x -> enumFromNTo x [|| 4 ||])
                    (enumFromNTo [|| 0 ||] [|| 4 ||])
-}

-}
