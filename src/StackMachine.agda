module StackMachine where

open import Data.Nat  
open import Data.List
open import Data.Bool
open import Data.Maybe
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

open ≡-Reasoning -- enables equational reasoning syntax

-- starting the definition of our source language

data BinOp : Set where
  plus mult : BinOp

data Exp : Set where
  const : ℕ → Exp
  op    : BinOp → Exp → Exp → Exp

-- denotation of operators

B⟦_⟧ : BinOp → (ℕ → ℕ → ℕ)
B⟦ plus ⟧ = _+_
B⟦ mult ⟧ = _*_

-- denotation of expressions

E⟦_⟧ : Exp → ℕ
E⟦ const n ⟧ = n
E⟦ op o e₁ e₂ ⟧ = B⟦ o ⟧ E⟦ e₁ ⟧ E⟦ e₂ ⟧

-- examples of source language

t01 : E⟦ const 42 ⟧ ≡ 42
t01 = refl

t02 : E⟦ op plus (const 2) (const 2) ⟧ ≡ 4
t02 = refl

t03 : E⟦ op mult (op plus (const 2) (const 2)) (const 7) ⟧ ≡ 28
t03 = refl

-- definition of our target language

data instr : Set where
  iconst : ℕ → instr
  iop    : BinOp → instr

prog : Set
prog = List instr

stack : Set 
stack = List ℕ

I⟦_⟧ : instr → stack → Maybe stack
I⟦ iconst n ⟧ s = just (n ∷ s)
I⟦ iop o ⟧ s with s
...| (v₁ ∷ v₂ ∷ s') = just (B⟦ o ⟧ v₁ v₂ ∷ s')
...| _              = nothing

P⟦_⟧ : prog → stack → Maybe stack
P⟦ [] ⟧ s = just s
P⟦ i ∷ p' ⟧ s with I⟦ i ⟧ s
... | just s' = P⟦ p' ⟧ s'
... | none    = none 

-- the expression compiler

C⟦_⟧ : Exp → prog
C⟦ const n ⟧ = iconst n ∷ []
C⟦ op o e₁ e₂ ⟧ with C⟦ e₁ ⟧ | C⟦ e₂ ⟧ 
... | c₁ | c₂ = c₂ ++ c₁ ++ (iop o) ∷ []

-- test cases for the compiler

t04 : C⟦ const 42 ⟧ ≡  [ iconst 42 ]
t04 = refl

t05 : C⟦ op plus (const 1) (const 2) ⟧
      ≡ iconst 2 ∷ iconst 1 ∷ iop plus ∷ []
t05 = refl

t06 : C⟦ op mult (op plus (const 1) (const 2)) (const 7) ⟧
      ≡ iconst 7 ∷ iconst 2 ∷ iconst 1 ∷ iop plus ∷ iop mult ∷ []
t06 = refl

t07 : P⟦ C⟦ const 42 ⟧ ⟧ []
      ≡ just [ 42 ]
t07 = refl

t08 : P⟦ C⟦ op plus (const 2) (const 2) ⟧ ⟧ []
      ≡ just [ 4 ]
t08 = refl

t09 : P⟦ C⟦ op mult (op plus (const 2) (const 2)) (const 7) ⟧ ⟧ []
      ≡ just [ 28 ]
t09 = refl

-- some simple lemmas. I believe that standard library has them, but
-- it uses records and modules and I don't understand these yet.

++-nil-end : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-nil-end [] = refl
++-nil-end (x ∷ xs) = 
  begin 
    (x ∷ xs) ++ [] ≡⟨ refl ⟩ 
    x ∷ (xs ++ []) ≡⟨ cong (_∷_ x) (++-nil-end xs) ⟩ 
    x ∷ xs 
  ∎

++-assoc : {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = 
  begin
    ((x ∷ xs) ++ ys) ++ zs ≡⟨ refl ⟩ 
    (x ∷ xs ++ ys) ++ zs ≡⟨ refl ⟩ 
    x ∷ (xs ++ ys) ++ zs ≡⟨ cong (_∷_ x) (++-assoc xs ys zs) ⟩ 
    (x ∷ xs ++ (ys ++ zs)) 
  ∎

C-correct' : ∀ (e : Exp)(p : prog)(s : stack) → P⟦ C⟦ e ⟧ ++ p ⟧ s ≡ P⟦ p ⟧ (E⟦ e ⟧ ∷ s)
C-correct' (const n) p s = refl
C-correct' (op o e e₁) p s =
  begin
    P⟦ C⟦ op o e e₁ ⟧ ++ p ⟧ s 
       ≡⟨ refl ⟩ 
    P⟦ ( (C⟦ e₁ ⟧ ++ (C⟦ e ⟧ ++ [ iop o ])) ++ p) ⟧ s
       ≡⟨ cong (λ z → P⟦ z ⟧ s) (++-assoc ( C⟦ e₁ ⟧ ) ( C⟦ e ⟧ ++ [ iop o ]) p ) ⟩
    P⟦ C⟦ e₁ ⟧ ++ ((C⟦ e ⟧ ++ [ iop o ]) ++ p) ⟧ s 
       ≡⟨ cong (λ z → P⟦ C⟦ e₁ ⟧ ++ z ⟧ s) (++-assoc ( C⟦ e ⟧ ) ( [ iop o ]) p) ⟩
    P⟦ C⟦ e₁ ⟧ ++ (C⟦ e ⟧ ++ ( [ iop o ] ++ p )) ⟧ s 
       ≡⟨ refl ⟩
    P⟦ C⟦ e₁ ⟧ ++ (C⟦ e ⟧ ++ ( iop o ∷ p )) ⟧ s 
       ≡⟨ C-correct' e₁ (C⟦ e ⟧ ++ (iop o) ∷ p) s ⟩ 
    P⟦ C⟦ e ⟧ ++ (iop o) ∷ p ⟧ ( E⟦ e₁ ⟧ ∷ s ) 
       ≡⟨ C-correct' e ((iop o) ∷ p) (E⟦ e₁ ⟧ ∷ s) ⟩ 
    P⟦ (iop o) ∷ p ⟧ (E⟦ e ⟧ ∷ E⟦ e₁ ⟧ ∷ s) 
       ≡⟨ refl ⟩
    P⟦ p ⟧ ((B⟦ o ⟧ E⟦ e ⟧ E⟦ e₁ ⟧) ∷ s) 
       ≡⟨ refl ⟩
    P⟦ p ⟧ (E⟦ op o e e₁ ⟧ ∷ s)
  ∎
  
-- finally the proof that the compiler preserves the semantics

C-correct : ∀ (e : Exp) → P⟦ C⟦ e ⟧ ⟧ [] ≡ just [ E⟦ e ⟧ ]
C-correct e =
  begin
    P⟦ C⟦ e ⟧ ⟧ []  
      ≡⟨ sym (cong (λ z → P⟦ z ⟧ []) (++-nil-end (C⟦ e ⟧))) ⟩ 
    P⟦ C⟦ e ⟧ ++ [] ⟧ []
      ≡⟨ C-correct' e [] [] ⟩
    P⟦ [] ⟧([ E⟦ e ⟧ ]) 
      ≡⟨ refl ⟩ 
    just ([ E⟦ e ⟧ ])
  ∎