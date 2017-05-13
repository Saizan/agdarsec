module Induction.Nat.StrongSized where

open import Relation.Unary.Indexed
open import Function
open import Size

infix 4 □_
record □_ (A : Size → Set) (n : Size) : Set where
  coinductive
  constructor mkBox
  field call : ∀ {m : Size< n} → A m
open □_ public

module _ {A B : Size → Set} where

 map : [ A ⟶ B ] → [ □ A ⟶ □ B ]
 call (map f A) = f (call A)

module _ {A : Size → Set} where

 extract : [ □ A ] → [ A ]
 extract a = call a

 duplicate : [ □ A ⟶ □ □ A ]
 call (call (duplicate A)) = call A

 lower : {n : Size}{m : Size< n} → (□ A) n → (□ A) m
 (lower A) = A

 fix□ : [ □ A ⟶ A ] → [ □ A ]
 call (fix□ f) = f (fix□ f)

module _ {A B : Size → Set} where

 map2 : {C : Size → Set} → [ A ⟶ B ⟶ C ] → [ □ A ⟶ □ B ⟶ □ C ]
 call (map2 f A B) = f (call A) (call B)

 app : [ □ (A ⟶ B) ⟶ (□ A ⟶ □ B) ]
 call (app F A) = call F (call A)

fix : ∀ A → [ □ A ⟶ A ] → [ A ]
fix A = extract ∘ fix□

module _ {A : Size → Set} where

 loeb : [ □ (□ A ⟶ A) ⟶ □ A ]
 loeb = fix (□ (□ A ⟶ A) ⟶ □ A) $ λ rec f → \ where
           .call -> call f (call rec (call (duplicate f)))

 loeb-direct : [ □ (□ A ⟶ A) ⟶ □ A ]
 loeb-direct f = app f (\ { .call → loeb f })
