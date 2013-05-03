module TypedExp where

open import Data.Unit
open import Data.Nat
open import Data.List 
open import Data.Bool
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

open ≡-Reasoning -- enables equational reasoning syntax

-- first, we define types

data Ty : Set where
  Nat Logic : Ty

-- now, type indexed operators and expressions

data Op : Ty → Ty → Ty → Set where
  Plus : Op Nat Nat Nat
  Mult : Op Nat Nat Nat
  Eq   : ∀ t → Op t t Logic 
  Lt   : Op Nat Nat Logic

data Exp : Ty → Set where
  NConst : ℕ → Exp Nat
  BConst : Bool → Exp Logic
  BOp    : ∀ { arg1 arg2 res } → Op arg1 arg2 res → Exp arg1 → Exp arg2 → Exp res

-- denotations of types and expressions

T⟦_⟧ : Ty → Set 
T⟦ Nat ⟧ = ℕ
T⟦ Logic ⟧ = Bool

_n≡_ : ℕ → ℕ → Bool
zero n≡ zero = true
suc n n≡ suc m = n n≡ m
_  n≡ _ = false

_n<_ : ℕ → ℕ → Bool
zero n< zero = false
zero n< _    = true
suc n n< suc m = n n< m
_ n< _ = false

_b≡_ : Bool → Bool → Bool
true b≡ b = b
false b≡ b = not b

O⟦_⟧ : { arg1 arg2 res : Ty } (o : Op arg1 arg2 res) → T⟦ arg1 ⟧ → T⟦ arg2 ⟧ → T⟦ res ⟧
O⟦ Plus ⟧ = _+_
O⟦ Mult ⟧ = _*_
O⟦ Eq t ⟧ with t 
...| Nat   = _n≡_ 
...| Logic = _b≡_
O⟦ Lt ⟧ = _n<_

E⟦_⟧ : {t : Ty} (e : Exp t) → T⟦ t ⟧ 
E⟦ NConst n ⟧ = n
E⟦ BConst b ⟧ = b
E⟦ BOp o e₁ e₂ ⟧ = O⟦ o ⟧ E⟦ e₁ ⟧ E⟦ e₂ ⟧

-- target language

tstack : Set
tstack = List Ty

data TInstr : tstack → tstack → Set where
  INConst : ∀ { s } → ℕ → TInstr s (Nat ∷ s)
  IBConst : ∀ { s } → Bool → TInstr s (Logic ∷ s)
  IOp     : ∀ {s : tstack}{arg1 arg2 res : Ty} → 
               Op arg1 arg2 res → 
                TInstr (arg1 ∷ arg2 ∷ s) (res ∷ s)

data TProg : tstack → tstack → Set where
  TNil  : ∀ { s } → TProg s s
  TCons : ∀ { s₁ s₂ s₃ } → TInstr s₁ s₂ → TProg s₂ s₃ → TProg s₁ s₃

-- defining the semantics

vstack : (ts : tstack) → Set
vstack [] = ⊤
vstack (t ∷ ts) = T⟦ t ⟧ × vstack ts

TI⟦_⟧ : ∀ {ts ts'}(i : TInstr ts ts') → vstack ts → vstack ts'
TI⟦ INConst n ⟧ s = n , s
TI⟦ IBConst b ⟧ s = b , s
TI⟦ IOp o ⟧ s with s
... | a , ( b , s') = O⟦ o ⟧ a b , s'

TP⟦_⟧ : ∀ {ts ts'}(p : TProg ts ts') → vstack ts → vstack ts'
TP⟦ TNil ⟧ = λ s → s
TP⟦ TCons i p' ⟧ = λ s → TP⟦ p' ⟧ ( TI⟦ i ⟧ s )

-- defining the compiler

tconcat : ∀ {ts ts' ts''} → TProg ts ts' → TProg ts' ts'' → TProg ts ts''
tconcat ( TNil ) = λ p → p
tconcat ( TCons i p ) = λ p' → TCons i (tconcat p p')

tcompile : ∀ {t} → Exp t → (ts : tstack) → TProg ts (t ∷ ts)
tcompile (NConst n) _ = TCons (INConst n) TNil
tcompile (BConst b) _ = TCons (IBConst b) TNil
tcompile (BOp o e e₁) ts = tconcat ( tcompile e₁ _ ) 
                                   ( tconcat ( tcompile e _ )
                                             ( TCons (IOp o) TNil ))

-- proving translation correctness

tconcat-correct : ∀ {t t' t''}(p : TProg t t')(p' : TProg t' t'')(s : vstack t) → TP⟦ tconcat p p' ⟧ s ≡ TP⟦ p' ⟧ (TP⟦ p ⟧ s)
tconcat-correct {.t'} {t'} TNil p' s = refl
tconcat-correct (TCons x p) p' s = tconcat-correct p p' (TI⟦ x ⟧ s)

tcompile_correct' : ∀ {t} → (e : Exp t) → (ts : tstack) → (s : vstack ts) → TP⟦ tcompile e ts ⟧ s ≡ ( E⟦ e ⟧ , s )
tcompile_correct' (NConst n) ts s = refl
tcompile_correct' (BConst b) ts s = refl
tcompile_correct' (BOp {t1} {t2} {t} o e e₁) ts s = 
  begin
     TP⟦ tcompile (BOp o e e₁) ts ⟧ s 
       ≡⟨ refl ⟩
     TP⟦ tconcat ( tcompile e₁ ts )
                 ( tconcat ( tcompile e (t2 ∷ ts) )
                           ( TCons (IOp o) TNil )) ⟧ s
       ≡⟨ tconcat-correct ( tcompile e₁ ts ) 
                          ( tconcat ( tcompile e (t2 ∷ ts) )
                                    ( TCons (IOp o) TNil )) 
                                      s ⟩ 
     TP⟦ tconcat ( tcompile e (t2 ∷ ts) )
                 ( TCons (IOp o) TNil ) ⟧ ( TP⟦ tcompile e₁ ts ⟧ s )
       ≡⟨ cong ( λ z → TP⟦ tconcat ( tcompile e (t2 ∷ ts) ) ( TCons (IOp o) TNil ) ⟧ z ) 
               ( tcompile_correct' e₁ ts s ) ⟩ 
     TP⟦ tconcat ( tcompile e (t2 ∷ ts) ) 
                 ( TCons (IOp o) TNil ) ⟧ ( E⟦ e₁ ⟧ , s ) 
       ≡⟨ tconcat-correct ( tcompile e (t2 ∷ ts) ) 
                          ( TCons (IOp o) TNil )
                          ( E⟦ e₁ ⟧ , s ) ⟩ 
     TP⟦ TCons (IOp o) TNil ⟧ ( TP⟦ tcompile e (t2 ∷ ts) ⟧ ( E⟦ e₁ ⟧ , s ))
       ≡⟨ cong (λ z → TP⟦ TCons (IOp o) TNil ⟧ z) ( tcompile_correct' e (t2 ∷ ts) ( E⟦ e₁ ⟧ , s ) )⟩ 

     TP⟦ TCons (IOp o) TNil ⟧ ( E⟦ e ⟧ , ( E⟦ e₁ ⟧ , s ) )
       ≡⟨ refl ⟩
     O⟦ o ⟧ E⟦ e ⟧ E⟦ e₁ ⟧ , s
       ≡⟨ refl ⟩ 
     E⟦ BOp o e e₁ ⟧ , s
  ∎     

tcompile_correct : ∀ {t} → (e : Exp t) → TP⟦ tcompile e [] ⟧ tt ≡ ( E⟦ e ⟧ , tt )
tcompile_correct e = tcompile_correct' e [] tt