--
--
-- ------------------------- Auxiliary functions (these are not written by me, apart from removeAll which is).

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: Eq a => [a] -> [a] -> [a]
removeAll x y = [n | n <- x, p n]
   where
     p xs = not (elem xs y)

fresh :: [Var] -> Var
fresh = head . removeAll variables


------------------------- Simple types

data Type = Base | Type :-> Type deriving (Eq)

--Nice is not written by me.
nice :: Type -> String
nice Base = "o"
nice (Base :-> b) = "o -> " ++ nice b
nice (   a :-> b) = "(" ++ nice a ++ ") -> " ++ nice b

instance Show Type where
  show = nice

type1 :: Type
type1 =  Base :-> Base

type2 :: Type
type2 = (Base :-> Base) :-> (Base :-> Base)


-- -- - - - - - - - - - - -- Terms (not written by me)
--
type Var = String
--
data Term =
    Variable Var
  | Lambda   Var Type Term
  | Apply    Term Term

--
pretty :: Term -> String
pretty = f 0
    where
      f i (Variable   x) = x
      f i (Lambda x t m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ": " ++ nice t ++ " . " ++ f 0 m
      f i (Apply    n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

instance Show Term where
  show = pretty
--
--
-- -- - - - - - - - - - - -- Numerals (These are not written by me).
--
numeral :: Int -> Term
numeral i = Lambda "f" (Base :-> Base) (Lambda "x" (Base) (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))
--
sucterm :: Term
sucterm =
    Lambda "m" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Variable "f") (Variable "x"))
    )))

addterm :: Term
addterm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
    ))))

multerm :: Term
multerm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Apply (Variable "m") (Apply (Variable "n") (Variable "f"))
    )))

suc :: Term -> Term
suc m = Apply sucterm m

add :: Term -> Term -> Term
add m n = Apply (Apply addterm m) n

mul :: Term -> Term -> Term
mul m n = Apply (Apply multerm m) n

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` (suc (numeral 2))

example3 :: Term
example3 = numeral 0 `mul` numeral 10

example4 :: Term
example4 = numeral 10 `mul` numeral 0

example5 :: Term
example5 = (numeral 2 `mul` numeral 3) `add` (numeral 5 `mul` numeral 7)

example6 :: Term
example6 = (numeral 2 `add` numeral 3) `mul` (numeral 3 `add` numeral 2)

example7 :: Term
example7 = numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` numeral 2)))
--
-- -- - - - - - - - - - - -- Renaming, substitution, beta-reduction
--

--Used is not written by me.
used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x t n) = [x] `merge` used n
used (Apply  n m) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z t n)
    | z == x    = Lambda (y) (t) (rename x y n)
    | otherwise = Lambda (z) (t) (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable m)
   | m == x = n
   | otherwise = Variable m
substitute replace replaceWith (Lambda binder type binded)
   | binder ==  replace = Lambda binder type binded
   | otherwise = Lambda (freshVar) (type) (substitute replace replaceWith (rename binder freshVar binded))
   where
     freshVar = fresh ((used binded) `merge` (used replaceWith) `merge` [binder] `merge` [replace])
substitute x y (Apply n m) = Apply (substitute x y n) (substitute x y m)


beta :: Term -> [Term]
beta (Apply (Lambda binder type bound) x) = [substitute binder x bound]
 ++ [Apply (Lambda binder type bound') x | bound' <- beta bound]
 ++ [Apply (Lambda binder type bound) x' | x' <- beta x]
beta (Apply x y) = [(Apply x' y) | x' <- beta x] ++ [(Apply x y') | y' <- beta y]
beta (Lambda x type y) = [(Lambda x type m) | m <- (beta y)]
beta (Variable _) = []

--
-- -- - - - - - - - - - - -- Normalize
--
normalize :: Term -> IO ()
normalize m = do
  putStr ((show (bound m)) ++ " -- ")
  print m
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)
--
--
-- -------------------------Type checking
--
--
type Context = [(Var, Type)]
-- -- --
--
searchContext :: Context -> Var -> Type
searchContext [] x = error "Variable not found."
searchContext (x:xs) var
  | (fst x) == var = snd x
  | otherwise = searchContext xs var

isEmpty :: [a] -> Bool
isEmpty [] = True
isEmpty _ = False

matches (a :-> b) c
  | a == c = b
matches _ _  = error "Type error"

typeof :: Context -> Term -> Type
typeof context (Variable x) = searchContext context x
typeof context (Lambda binder t bound) = (searchContext ((binder, t):context) binder) :-> (typeof ((binder,t):context) bound)
typeof context (Apply m n) = matches (typeof context m) (typeof context n)

-- --
-- --
example8 = Lambda "x" Base ((Apply (Apply (Variable "f") (Variable "x")) (Variable "x")))
--
--
--
-- ------------------------- Assignment 3: Functionals (Functional, Show and fun not written by me).
--
data Functional =
    Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f

-- -- - - - - - - - - - - -- Constructing functionals
--
dummy :: Type -> Functional
dummy Base = Num 0
dummy (m :-> n) = Fun (\x -> (dummy n))
--
count :: Type -> Functional -> Int
count Base (Num n) = n
count (m :-> n) (Fun f) = count n (f (dummy m))
--
increment :: Functional -> Int -> Functional
increment (Num k) n = (Num (k + n))
increment (Fun f) n = Fun (\x -> increment (f x) n)
--
--
-- ------------------------- Assignment 4 : Counting reduction steps
--
type Valuation = [(Var, Functional)]
--
searchValuation :: Valuation -> Var -> Functional
searchValuation [] x = error "Variable not found in valuation."
searchValuation (x:xs) var
  | (fst x) == var = snd x
  | otherwise = searchValuation xs var

interpret :: Context -> Valuation -> Term -> Functional
interpret c v (Variable t) = searchValuation v t
interpret c v (Lambda binder t bound) = Fun (\x -> interpret ((binder, t):c) ((binder, x):v) bound)
interpret c v (Apply m n) = increment ((fun (interpret c v m)) (interpret c v n)) (1 + (count (typeof c n) (interpret c v n)))
--
bound :: Term -> Int
bound x = count (typeof [] x) (interpret [] [] x)
