{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedLists #-}
module Numeric.LinearAlgebra.Lin where

import Prelude hiding (foldr)
import GHC.TypeLits
import GHC.Exts (IsList(..))

import Control.DeepSeq (NFData(..))
import Data.Foldable (Foldable, foldr)
import Data.Traversable (Traversable)
import Control.Applicative (Applicative(..), (<$>))
import Control.Monad (forM_)
import Control.Monad.ST (runST)

import qualified Data.Vector as V
import qualified Data.Vector.Generic as GV
import qualified Data.Vector.Mutable as MV

newtype Vect (n :: Nat) a = Vect (V.Vector a)
  deriving (Eq, Ord, Functor, Foldable, Traversable, NFData)
unVec :: Vect l a -> V.Vector a
unVec (Vect v) = v

instance Show a => Show (Vect n a) where
    show (Vect vec) = "| " ++ show' vec ++ "|"
      where
        show' xs
            | V.null xs = ""
            | otherwise = show (V.head xs) ++ " " ++ show' (V.tail xs)

instance Applicative (Vect n) where
    pure = Vect . V.singleton
    (<*>) (Vect funcs) (Vect vect) = Vect $
        V.generate (V.length vect) (\i -> (funcs V.! i) (vect V.! i))

instance IsList (Vect n a) where
    type Item (Vect l a) = a
    fromList = Vect . V.fromList
    toList = V.toList . unVec

newtype Matrix w h a = Matrix (Vect h (Vect w a))
  deriving (Eq, Ord, Functor, Foldable, Traversable, NFData)
unMat :: Matrix w h a -> Vect h (Vect w a)
unMat (Matrix v) = v

instance Show a => Show (Matrix w h a) where
    show (Matrix mat) = foldr (\x accum -> accum ++ show x ++ "\n") "" mat

-- = Vect construction.

listToVec :: [a] -> Vect n a
listToVec = Vect . V.fromList

listToVecN :: Int -> [a] -> Vect n a
listToVecN n = Vect . V.fromListN n

empty :: Vect 0 a
empty = Vect V.empty

nil :: Vect 0 a
nil = Vect V.empty

vec2 :: a -> a -> Vect 2 a
vec2 x y = Vect $ V.fromListN 2 [x, y]
vec3 :: a -> a -> a -> Vect 3 a
vec3 x y z = Vect $ V.fromListN 3 [x, y, z]
vec4 :: a -> a -> a -> a -> Vect 4 a
vec4 x y z w = Vect $ V.fromListN 4 [x, y, z, w]

(&) :: a -> Vect l a -> Vect (l + 1) a
(&) val (Vect vec) = Vect $ V.cons val vec
infixr 5 &

(+&) :: Vect len1 a -> Vect len2 a -> Vect (len1 + len2) a
(+&) (Vect v1) (Vect v2) = Vect $ v1 V.++ v2
infixr 5 +&

-- = Matrix Construction.

row :: Vect l a -> Matrix l 1 a
row r = Matrix $ Vect $ V.singleton r

(|&) :: Matrix w h1 a -> Matrix w h2 a -> Matrix w (h1 + h2) a
(|&) (Matrix (Vect m1)) (Matrix (Vect m2)) =
    Matrix . Vect $ m1 V.++ m2
infixr 4 |&

identity :: Num a => Matrix 4 4 a
identity = Matrix . Vect $
    V.fromListN 4 [vec4 1 0 0 0,
                   vec4 0 1 0 0,
                   vec4 0 0 1 0,
                   vec4 0 0 0 1]
{-
    row (vec4 1 0 0 0) |&
    row (vec4 0 1 0 0) |&
    row (vec4 0 0 1 0) |&
    row (vec4 0 0 0 1)
-}

-- = Matrix operations.

multmm :: Num a => Matrix w l a -> Matrix l h a -> Matrix w h a
multmm m1 (Matrix m2) =
    let m1' = unMat $ transpose m1
    in Matrix $ fmap (\r -> fmap (dot r) m1') m2

multmv :: Num a => Matrix w h a -> Vect h a -> Vect w a
multmv mat vec = fmap (dot vec) (unMat $ transpose mat)

perspective :: Floating a =>
    a ->
    a ->
    a ->
    a ->
    Matrix 4 4 a
perspective near far fovy aspect = Matrix . Vect $
    V.fromListN 4
        [vec4 (2*n/(r-l)) 0 (-(r+l)/(r-l)) 0,
         vec4 0 (2*n/(t-b)) ((t+b)/(t-b)) 0,
         vec4 0 0 (-(f+n)/(f-n)) (-2*f*n/(f-n)),
         vec4 0 0 (-1) 0]
{-
    row (vec4 (2*n/(r-l)) 0 (-(r+l)/(r-l)) 0)    |&
    row (vec4 0 (2*n/(t-b)) ((t+b)/(t-b)) 0)     |&
    row (vec4 0 0 (-(f+n)/(f-n)) (-2*f*n/(f-n))) |&
    row (vec4 0 0 (-1) 0)
-}
  where
    n = near
    f = far
    t = n * tan (fovy/2)
    b = -t
    r = aspect*t
    l = -r

transpose :: Matrix w h a -> Matrix h w a
transpose (Matrix (Vect vec)) =
    let width = V.length . unVec $ V.head vec
        height = V.length vec

        vec' = Vect $ V.generate width
            (\i -> Vect $ V.generate height
                (\j -> unVec (vec V.! j) V.! i))
    in Matrix vec'

translation :: Num a => Vect 3 a -> Matrix 4 4 a
translation = flip translate identity

translate :: Vect 3 a -> Matrix 4 4 a -> Matrix 4 4 a
translate (Vect vec) (Matrix (Vect mat)) = runST $ do
    mutMat <- GV.unsafeThaw mat
    mutRow <- GV.unsafeThaw (unVec $ mat V.! 3)
    MV.unsafeWrite mutRow 0 (vec V.! 0)
    MV.unsafeWrite mutRow 1 (vec V.! 1)
    MV.unsafeWrite mutRow 2 (vec V.! 2)
    MV.unsafeWrite mutMat 3 . Vect =<< V.unsafeFreeze mutRow
    Matrix . Vect <$> V.unsafeFreeze mutMat

scaling :: Num a => Vect 3 a -> Matrix 4 4 a
scaling = flip scale identity

scale :: Vect 3 a -> Matrix 4 4 a -> Matrix 4 4 a
scale (Vect v) (Matrix (Vect m)) = runST $ do
    mutMat <- GV.unsafeThaw m
    forM_ [0..2] $ writeRow v mutMat
    Matrix . Vect <$> V.unsafeFreeze mutMat
  where
    writeRow vec mutMat i = do
        mutRow <- GV.unsafeThaw . unVec =<< MV.unsafeRead mutMat i
        MV.unsafeWrite mutRow i (vec V.! i)
        MV.unsafeWrite mutMat i . Vect =<< V.unsafeFreeze mutRow

rotation :: Floating a => Vect 3 a -> Matrix 4 4 a
rotation (Vect rot) =
    rotationX (rot V.! 0) `multmm`
    rotationY (rot V.! 1) `multmm`
    rotationZ (rot V.! 2)

rotationX :: Floating a => a -> Matrix 4 4 a
rotationX x = Matrix . Vect . V.fromListN 4 $
    [listToVecN 4 [1, 0, 0, 0],
     listToVecN 4 [0, cos x, -sin x, 0],
     listToVecN 4 [0, sin x, cos x, 0],
     listToVecN 4 [0, 0, 0, 1]]
rotationY :: Floating a => a -> Matrix 4 4 a
rotationY y = Matrix . Vect . V.fromListN 4 $
    [listToVecN 4 [cos y, 0, sin y, 0],
     listToVecN 4 [0, 1, 0, 0],
     listToVecN 4 [-sin y, 0, cos y, 0],
     listToVecN 4 [0, 0, 0, 1]]
rotationZ :: Floating a => a -> Matrix 4 4 a
rotationZ z = Matrix . Vect . V.fromListN 4 $
    [listToVecN 4 [cos z, -sin z, 0, 0],
     listToVecN 4 [sin z, cos z, 0, 0],
     listToVecN 4 [0, 0, 1, 0],
     listToVecN 4 [0, 0, 0, 1]]

-- = Vect operations.

(!) :: Vect l a -> Int -> a
(!) (Vect v) i = v V.! i

normalize :: Floating a => Vect l a -> Vect l a
normalize vec = fmap (/ sqrt (dot vec vec)) vec

dot :: Num a => Vect l a -> Vect l a -> a
dot (Vect u) (Vect v) = V.foldr (+) 0 (V.zipWith (*) u v)

cross :: Num a => Vect 3 a -> Vect 3 a -> Vect 3 a
cross u v =
    let ux = u ! 0
        uy = u ! 1
        uz = u ! 2
        vx = v ! 0
        vy = v ! 1
        vz = v ! 2
    in Vect $ V.fromList [uy*vz-uz*vy, uz*vx-ux*vz, ux*vy-uy*vx]

append :: Vect len1 a -> Vect len2 a -> Vect (len1 + len2) a
append (Vect a) (Vect b) = Vect $ a V.++ b

-- = Testing.

testVal :: Matrix 4 4 Int
testVal =
    row [1, 2, 3, 4]    |&
    row [5, 6, 7, 8]    |&
    row [9, 10, 11, 12] |&
    row [13, 14, 15, 16]

test :: Matrix 4 4 Float
test = perspective 12 4 60 (800/600)

main :: IO ()
main = print $ foldr
    (\_ b -> b `multmm` rotation [0.351451, 0.1426, 0.9837::Float])
    identity ([0..10000] :: [Int])
