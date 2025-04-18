-- ## Lean 4 実装：意味付き CCG 導出
-- 構文カテゴリ
inductive Cat : Type
| S | NP
| Slash : Cat → Cat → Cat   -- A / B
| BSlash : Cat → Cat → Cat  -- A \ B
deriving Repr, DecidableEq

open Cat

-- 意味項（簡易ラムダ式）
inductive Sem : Type
| var : String → Sem
| app : Sem → Sem → Sem
| lam : String → Sem → Sem
| const : String → Sem
deriving Repr

open Sem

-- 辞書エントリ
structure LexiconEntry where
  word : String
  cat  : Cat
  sem  : Sem
deriving Repr

-- 意味合成付き導出構造
inductive Derivation : Cat → Type
| leaf : (e : LexiconEntry) → Derivation e.cat
| fa   : ∀ {A B : Cat}, Derivation (Slash A B) → Derivation B → Derivation A
| ba   : ∀ {A B : Cat}, Derivation B → Derivation (BSlash A B) → Derivation A

open Derivation

-- 意味合成を計算する関数（構文木に意味を割り当てる）
def getSem : ∀ {C : Cat}, Derivation C → Sem
| _, leaf e      => e.sem
| _, fa f a      => app (getSem f) (getSem a)
| _, ba a f      => app (getSem f) (getSem a)

-- ## 語彙定義（ラムダ式付き）
-- (S\NP)/NP 他動詞
def TV : Cat := Slash (BSlash S NP) NP

def john : LexiconEntry :=
  { word := "John", cat := NP, sem := const "john" }

def mary : LexiconEntry :=
  { word := "Mary", cat := NP, sem := const "mary" }

def loves : LexiconEntry :=
  { word := "loves", cat := TV,
    sem := lam "x" (lam "y" (app (app (const "love") (var "y")) (var "x"))) }

-- ## 導出木
-- 構文導出と意味合成
def johnD : Derivation NP := leaf john
def maryD : Derivation NP := leaf mary
def lovesD : Derivation TV := leaf loves

def lovesMary : Derivation (BSlash S NP) :=
  fa lovesD maryD

def fullSentence : Derivation S :=
  ba johnD lovesMary

#eval getSem fullSentence
-- => love john mary （実際はラムダ項: ((λx.λy.love y x) mary) john）

-- Sem.app
--   (Sem.app
--     (Sem.lam "x" (Sem.lam "y" (Sem.app (Sem.app (Sem.const "love") (Sem.var "y")) (Sem.var "x"))))
--     (Sem.const "mary"))
--   (Sem.const "john")
