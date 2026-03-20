{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase   #-}
module Generator
  (run, examples, solve)
where
import           Control.Monad (ap, liftM)

type Loc = String
type Error = String
type Store = [(Loc, Type)]

data Type
  = TInt
  | TBool
  | TFun Type Type
  | TPair Type Type
  | TSum Type Type
  | TCand Int

instance Show Type where
  show :: Type -> String
  show TInt          = "int"
  show TBool         = "bool"
  show (TFun t1 t2)  = show t1 <> " -> " <> show t2
  show (TPair t1 t2) = show t1 <> " x " <> show t2
  show (TSum t1 t2)  = show t1 <> " + " <> show t2
  show (TCand i)     = show i

data Constraint = CCand Type Type | CVerified Type Type

instance Show Constraint where
  show :: Constraint -> String
  show (CCand t1 t2)     = show t1 <> " = " <> show t2
  show (CVerified t1 t2) = show t1 <> " =V " <> show t2

data Term
  = Var Loc
  | Num Int
  | Bin Bool
  | Plus Term Term
  | Leq Term Term
  | If Term Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Lam Loc Term
  | App Term Term
  | Let Loc Term Term
  | Rec Loc Term
  | Inl Term
  | Inr Term
  | Case Term Loc Term Loc Term

instance Show Term where
  show :: Term -> String
  show t =
    case t of
      Var x -> x
      Num x -> show x
      Bin x -> show x
      Plus t1 t2 -> show t1 <> " + " <> show t2
      Leq t1 t2 -> show t1 <> " <= " <> show t2
      If t1 t2 t3 -> "if " <> show t1 <> " then " <> show t2 <> " else " <> show t3
      Pair t1 t2 -> "(" <> show t1 <> ", " <> show t2 <> ")"
      Fst t1 -> "fst(" <> show t1
      Snd t1 -> "snd(" <> show t1
      Lam x t1 -> "\\" <> x <> ". " <> show t1
      App t1 t2 -> show t1 <> " " <> show t2
      Let x t1 t2 -> "let " <> show x <> " <= " <> show t1 <> " in " <> show t2
      Rec f t1 -> "rec " <> f <> ". " <> show t1
      Inl t0 -> "inl(" <> show t0 <> ")"
      Inr t0 -> "inr(" <> show t0 <> ")"
      Case t0 x1 t1 x2 t2 -> "case " <> show t0 <> " of inl(" <> x1 <> ") => " <> show t1 <> ", inr(" <> x2 <> ") => " <> show t2

newtype RS a = RS (Store -> Int -> (Either Error a, Int))

instance Monad RS where
  (>>=) :: RS a -> (a -> RS b) -> RS b
  RS x >>= f = RS $ \store i ->
    case x store i of
      (Left err, i') -> (Left err, i')
      (Right x', i') ->
        let RS y = f x'
        in  y store i'

instance Functor RS where
  fmap :: (a -> b) -> RS a -> RS b
  fmap = liftM

instance Applicative RS where
  pure :: a -> RS a
  pure x = RS $ \_env state -> (Right x, state)
  (<*>) :: RS (a -> b) -> RS a -> RS b
  (<*>) = ap

getI :: RS Int
getI = RS $ \_env i -> (Right i, i + 1)

getStore :: RS Store
getStore = RS $ \store i -> (Right store, i)

local :: (Store -> Store) -> RS (Type, [Constraint]) -> RS (Type, [Constraint])
local f (RS g) = RS $ \env state -> g (f env) state

failure :: String -> RS (Type, [Constraint])
failure s = RS $ \_env i -> (Left s, i)

eval :: Term -> RS (Type, [Constraint])
eval t =
  case t of
    Var loc -> do
      store <- getStore
      case lookup loc store of
        Nothing -> failure "Could not find variable in store."
        Just t' -> return (t', [])
    Num _ -> pure (TInt, [])
    Bin _ -> pure (TBool, [])
    Plus t0 t1 -> do
      (t0', c0) <- eval t0
      (t1', c1) <- eval t1
      return (
          TInt,
          c0 <>
          c1 <>
          [CCand t0' TInt, CCand t1' TInt]
        )
    Leq t0 t1 -> do
      (t0', c0) <- eval t0
      (t1', c1) <- eval t1
      return (
          TBool,
          c0 <>
          c1 <>
          [CCand t0' TInt, CCand t1' TInt]
        )
    If t0 t1 t2 -> do
      (t0', c0) <- eval t0
      (t1', c1) <- eval t1
      (t2', c2) <- eval t2
      return (
          t1',
          c0 <>
          c1 <>
          c2 <>
          [CCand t0' TBool, CCand t1' t2']
        )
    Pair t1 t2 -> do
      (t1', c1) <- eval t1
      (t2', c2) <- eval t2
      return (
          TPair t1' t2',
          c1 <>
          c2 <>
          []
        )
    Fst t0 -> do
      (t0', c0) <- eval t0
      i' <- getI
      _ <- getI
      return (
          TCand i',
          c0 <>
          [CCand t0' $ TSum (TCand i') (TCand $ i' + 1)]
        )
    Snd t0 -> do
      (t0', c0) <- eval t0
      i' <- getI
      _ <- getI
      return (
          TCand $ i' + 1,
          c0 <>
          [CCand t0' $ TSum (TCand i') (TCand $ i' + 1)]
        )
    Lam x t0 -> do
      i <- getI
      (t0', c0) <- local ((x, TCand i) :) $ eval t0
      return (
          TFun (TCand i) t0',
          c0
        )
    App t1 t2 -> do
      (t1', c1) <- eval t1
      (t2', c2) <- eval t2
      i' <- getI
      return (
          TCand i',
          c1 <>
          c2 <>
          [CCand t1' (TFun t2' $ TCand i')]
        )
    Let x t1 t2 -> do
      (t1', c1) <- eval t1
      (t2', c2) <- local ((x, t1') :) $ eval t2
      return (
          t2',
          c1 <>
          c2
        )
    Rec x t0 -> do
      i <- getI
      (t0', c0) <- local ((x, TCand i) :) $ eval t0
      return (
          t0',
          c0 <>
          [CCand (TCand i) t0']
        )
    Inl t0 -> do
      (t0', c0) <- eval t0
      i' <- getI
      return (
          TSum t0' $ TCand i',
          c0
        )
    Inr t0 -> do
      (t0', c0) <- eval t0
      i' <- getI
      return (
          TSum (TCand i') t0',
          c0
        )
    Case t0 x1 t1 x2 t2 -> do
      (t0', c0) <- eval t0
      i'' <- getI
      (t1', c1) <- local ((x1, TCand i'') :) $ eval t1
      i''' <- getI
      (t2', c2) <- local ((x2, TCand i''') :) $ eval t2

      return (
          t1',
          c0 <>
          c1 <>
          c2 <>
          [CCand t1' t2', CCand t0' $ TSum (TCand i'') $ TCand i''']
        )


examples :: [Term]
examples = [
    -- Num 1,
    -- Plus (Num 1) (Num 2),
    -- Leq (Num 1) (Num 2),
    -- If (Leq (Num 1) (Num 2)) (Num 2) (Num 3),
    -- Fst (Num 1),
    -- Snd (Num 1),
    -- Plus (Num 3) (Bin True),
    Rec "f" $ Lam "x" $ Lam "y" $ If (Leq (Num 0) $ Var "x") (Var "y") $ App (App (Var "f") $ Plus (Var "x") $ Num 1) $ Var "y",
    Lam "x" $ Case (Var "x") "y" (Var "x") "z" (Inl $ Var "z")
  ]

-- runEval :: RS (Either String (Type, [Constraint])) ->

runEval :: RS (Type, [Constraint]) -> Either String (Type, [Constraint])
runEval (RS m) = fst $ m [] 0

run :: Term -> Either String (Type, [Constraint])
run = runEval . eval

isInUV :: Int -> Type -> Bool
isInUV x t =
  case t of
    TInt        -> False
    TBool       -> False
    TFun t1 t2  -> f t1 || f t2
    TPair t1 t2 -> f t1 || f t2
    TSum t1 t2  -> f t1 || f t2
    TCand x'    -> x == x'
  where f = isInUV x

substitude :: Type -> Type -> Int -> Type
substitude t x' x = substitude' t
  where
    substitude' t' =
      case t' of
        TInt                 -> TInt
        TBool                -> TBool
        TFun t1 t2           -> TFun (f t1) $ f t2
        TPair t1 t2          -> TPair (f t1) $ f t2
        TSum t1 t2           -> TSum (f t1) $ f t2
        TCand x'' | x'' == x -> x'
        TCand x''            -> TCand x''
    f  = substitude'

solve :: (Type, [Constraint]) -> (Type, [Constraint])
solve (t, cs) =
  let cs' = csolve cs
  in
    case cIsSuccess cs' of
      False -> (t, cs')
      True ->
        let converted = cconvert cs'
            t' = foldl (\acc (x, t1) -> substitude acc t1 x) t converted
        in  (t', cs')

cconvert :: [Constraint] -> [(Int, Type)]
cconvert []                             = []
cconvert ((CVerified (TCand x) t) : cs) = (x, t) : (cconvert cs)
cconvert _                              = error "Fatal cconvert error."

cIsSuccess :: [Constraint] -> Bool
cIsSuccess []                             = True
cIsSuccess ((CVerified (TCand _) _) : cs) = cIsSuccess cs
cIsSuccess _                              = False

csolve :: [Constraint] -> [Constraint]
csolve [] = []
csolve (c : cs) =
  case c of
    CVerified _ _ -> ccs
    CCand TInt TInt -> csolve cs
    CCand TBool TBool -> csolve cs
    CCand (TPair t1 t2) (TPair t1' t2') -> csolve $ [CCand t1 t1', CCand t2 t2'] <> cs
    CCand (TFun t1 t2) (TFun t1' t2') -> csolve $ [CCand t1 t1', CCand t2 t2'] <> cs
    CCand (TSum t1 t2) (TSum t1' t2') -> csolve $ [CCand t1 t1', CCand t2 t2'] <> cs
    CCand TInt TBool -> ccs
    CCand TInt (TPair _ _) -> ccs
    CCand TInt (TFun _ _) -> ccs
    CCand TInt (TSum _ _) -> ccs
    CCand TBool TInt -> ccs
    CCand TBool (TPair _ _) -> ccs
    CCand TBool (TFun _ _) -> ccs
    CCand TBool (TSum _ _) -> ccs
    CCand (TPair _ _) TInt -> ccs
    CCand (TPair _ _) TBool -> ccs
    CCand (TPair _ _) (TFun _ _) -> ccs
    CCand (TPair _ _) (TSum _ _) -> ccs
    CCand (TFun _ _) TInt -> ccs
    CCand (TFun _ _) TBool -> ccs
    CCand (TFun _ _) (TPair _ _) -> ccs
    CCand (TFun _ _) (TSum _ _) -> ccs
    CCand (TSum _ _) TInt -> ccs
    CCand (TSum _ _) TBool -> ccs
    CCand (TSum _ _) (TPair _ _) -> ccs
    CCand (TSum _ _) (TFun _ _) -> ccs
    CCand (TCand x1) (TCand x2) | x1 == x2 -> csolve cs
    CCand (TCand x) t | isInUV x t -> ccs
    CCand t (TCand x) | isInUV x t -> ccs
    CCand (TCand x) t -> csolve $ map
      ( \case
          CCand t1 t2 -> CCand (substitude t1 t x) $ substitude t2 t x
          CVerified t1 t2 -> CVerified (substitude t1 t x) $ substitude t2 t x
      ) cs
      <> [CVerified (TCand x) t]
    CCand t (TCand x) -> csolve $ map
      ( \case
          CCand t1 t2 -> CCand (substitude t1 t x) $ substitude t2 t x
          CVerified t1 t2 -> CVerified (substitude t1 t x) $ substitude t2 t x
      ) cs
      <> [CVerified t (TCand x)]
  where ccs = c : cs
