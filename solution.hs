import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)
import Data.Char
--
--
-- The data type for algebraic expressions
--
data ME = Num Int 
          | Var Char
          | Group ME
          | Add ME ME
          | Sub ME ME
          | Mul ME ME
          | Power ME Int
          | Neg ME
          deriving (Show, Ord, Eq)


deriv :: ME -> Char -> ME

deriv (Num _) x = Num 0
deriv (Var y) x
  | x == y      = Num 1
  | otherwise   = Num 0
deriv (Group f) x = deriv f x
deriv (Add f g) x = Add (deriv f x) (deriv g x)
deriv (Sub f g) x = Sub (deriv f x) (deriv g x)
deriv (Mul f g) x = Add (Mul g (deriv f x)) (Mul f (deriv g x)) 
deriv (Neg f) x = Neg (deriv f x)
deriv (Power f n) x 
  | n == 0      = Num 0
  | otherwise   = Mul (Mul (Num n) (Power f (n - 1))) (deriv f x)


simplify (Num n) = (Num n)
simplify (Var v) = (Var v)
simplify (Group e) = simplify e
simplify (Add f g) = makeAdd (simplify f) (simplify g)
simplify (Sub f g) = makeSub (simplify f) (simplify g)
simplify (Mul f g) = makeMul (simplify f) (simplify g)
simplify (Power f n) = makePower (simplify f) n
simplify (Neg f) = makeNeg (simplify f)


makeAdd f (Num 0) = f
makeAdd (Num m) (Num n) = Num k where k = m + n
makeAdd (Num n) f = makeAdd f (Num n)
makeAdd (Add f (Num m)) (Num n) = makeAdd f (Num (m + n))
makeAdd (Add f (Num n)) g = makeAdd f (makeAdd g (Num n))
makeAdd (Mul (Num m) f) (Mul (Num n) f2)
    | f == f2        =  Mul (Num (m + n)) f
    | otherwise       = Add (Mul (Num m) f) (Mul (Num n) f2)
makeAdd f g = Add f g


makeSub (Num m) (Num n) = Num (m - n)
makeSub e (Num 0) = e
makeSub (Num 0) e = makeNeg e
makeSub (Num n) e = makeAdd (Neg e) (Num n)
makeSub (Sub e (Num m)) (Num n) = makeSub e (Num (m + n))
makeSub f g = Sub f g


makeMul (Num m) (Num n) = Num (m * n)
makeMul (Num 0) f = Num 0
makeMul (Num 1) f = f
makeMul f (Num n) = makeMul (Num n) f
makeMul (Power f m) (Power g n)
    | f == g        = Power g (m + n)     
	  | otherwise     = Mul (Power f m) (Power g n)
makeMul (Power f n) g = makeMul g (Power f n)
makeMul f (Mul g h) = makeMul (makeMul f g) h
makeMul f g = Mul f g

makePower f 0 = Num 1
makePower f 1 = f
makePower (Num m) n = Num (m ^ n)
makePower f n = Power f n

makeNeg (Neg e) = e
makeNeg e = Neg e


-- The Unparser

unparse (Num n) = show n
unparse (Var x) = [x]
unparse (Add f g) = unparse f ++ "+" ++ unparse (forceTerm g)
unparse (Sub f g) = unparse f ++ "-" ++ unparse (forceTerm g)
unparse (Mul f g) = unparse (forceTerm f) ++ "*" ++ unparse (forceFactor g)
unparse (Power f n) = unparse (forceElement f) ++ "**" ++ show n
unparse (Group f) = "(" ++ unparse f ++ ")"
unparse (Neg f) = "-" ++ unparse (forceTerm f)

forceTerm (Add f g) = Group (Add f g)
forceTerm (Sub f g) = Group (Sub f g)
forceTerm (Neg f) = Group (Neg f)
forceTerm x = x

forceFactor (Mul f g) = Group (Mul f g)
forceFactor x = forceTerm x

forceElement (Power f n) = Group (Power f n)
forceElement x = forceFactor x

-- The Parser

parseExpr :: [Char] -> Maybe (ME, [Char])
parseTerm :: [Char] -> Maybe (ME, [Char])
parseFactor :: [Char] -> Maybe (ME, [Char])
parseElement :: [Char] -> Maybe (ME, [Char])



parseElement ('(':more) =
    case parseExpr(more) of
        Just (e, ')':yet_more) -> Just(Group e, yet_more)
        _ -> Nothing
parseElement (c:cs)
  | isAlpha c     =  Just (Var c, cs)
  | otherwise     =  case parseNumeral (c:cs) of 
                        Just (n, s) -> Just (Num n, s)
                        _ -> Nothing


parseNumeral "" = Nothing
parseNumeral (c:cs)
  | isDigit c     =  extendNum (digitToInt c) cs
  | otherwise     =  Nothing

extendNum accum "" = Just (accum, "")
extendNum accum (c : cs) 
  | isDigit c     =  extendNum (10 * accum + (digitToInt c)) cs
  | otherwise     =  Just (accum, c:cs)


parseFactor s =
  case parseElement(s) of
    Just (e, '*':'*':more) -> 
      case parseNumeral more of
        Just (n, yet_more) -> Just (Power e n, yet_more)
        _ -> Nothing
    Just (e, more) -> Just (e, more)
    _ -> Nothing

parseTerm s =
    case parseFactor(s) of
        Just (e, more_chars) -> extendTerm(e, more_chars)
        _ -> Nothing


extendTerm (e1, []) = Just (e1, [])
extendTerm (e1, '*' : more) =
    case parseFactor(more) of 
        Just(e2, yet_more) -> extendTerm(Mul e1 e2, yet_more)
        _ -> Nothing
extendTerm(e1, c:more) = Just (e1, c:more)

parseExpr ('-':more) =
    case parseTerm(more) of
        Just (e, yet_more) -> Just (Neg e, yet_more)
        _ -> Nothing
parseExpr s =
    case parseTerm(s) of
        Just(e, more) -> extendExpr(e, more)
        _ -> Nothing

extendExpr (e1, []) = Just (e1, [])
extendExpr (e1, '+' : more) =
    case parseTerm(more) of 
        Just(e2, yet_more) -> extendExpr(Add e1 e2, yet_more)
        _ -> Nothing
extendExpr (e1, '-' : more) =
    case parseTerm(more) of 
        Just(e2, yet_more) -> extendExpr(Sub e1 e2, yet_more)
        _ -> Nothing
extendExpr(e1, s) = Just (e1, s)


parseME s = 
  case parseExpr s of
    Just (e, "") -> Just e
    _ -> Nothing

-- Main Program

parse_deriv_simp_unparse s v =
  case parseME s of
    Just e -> Just (unparse (deriv e v))
    _ -> Nothing

main = do
  [expr, v:cs] <- getArgs
  case parse_deriv_simp_unparse expr v of
    Just s -> hPutStrLn stdout s
    _ -> hPutStrLn stdout "Parse failure"







