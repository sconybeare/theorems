module Pigeonhole where

open import Level using (Level; _⊔_)
open import Data.Nat as Nat
open import Data.Vec
open import Data.Fin
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary
open import Data.Empty

collisionType : (n : ℕ) → (m : ℕ) → (Fin m → Fin n) → Fin m → Set
collisionType n m f k = Σ (Fin m) (λ k′ → (k′ ≢ k) × (f k ≡ f k′))

checkZeroCollision : (m : ℕ) → (f : Fin (suc m) → ℕ) → Dec (Σ (Fin m) (λ x → f (Fin.suc x) ≡ f Fin.zero))
checkZeroCollision zero f = no contr
  where
    contr : ¬ Σ (Fin zero) (λ z → f (suc z) ≡ f zero)
    contr (() , _)
checkZeroCollision (suc m-1) f with (f $ suc zero) ≟ f zero
checkZeroCollision (suc m-1) f | yes p = yes (zero , p)
checkZeroCollision (suc zero) f | no ¬p = no contr
  where
    contr : (x : Σ (Fin (suc zero)) (λ z → f (suc z) ≡ f zero)) → ⊥
    contr (zero , proj₂) = ¬p proj₂
    contr (suc () , proj₂)
checkZeroCollision (suc (suc m-2)) f | no ¬p with checkZeroCollision (suc m-2) g
  where
    g : Fin (suc (suc m-2)) → ℕ
    g zero = f zero
    g (suc x) = f (suc (suc x))
checkZeroCollision (suc (suc m-2)) f | no ¬p | yes (proj₁ , proj₂) = yes (suc proj₁ , proj₂)
checkZeroCollision (suc (suc m-2)) f | no ¬p | no ¬p₁ = no (¬p₁ ∘ red)
  where
    red : Σ (Fin (suc (suc m-2))) (λ z → f (suc z) ≡ f zero) →
          Σ (Fin (suc m-2)) (λ z → f (suc (suc z)) ≡ f zero)
    red (zero , proj₂) = ⊥-elim (¬p proj₂)
    red (suc proj₁ , proj₂) = proj₁ , proj₂

isInjective : ∀ {A B} → (A → B) → Set
isInjective {A} f = ∀ (x y : A) → (f x) ≡ (f y) → x ≡ y

_∼_ : ∀ {A B} → (f : A → B) → (g : A → B) → Set
f ∼ g = ∀ x → (f x ≡ g x)

-- hasRetract⇒isInjective : ∀ {A B} (f : A → B) → (g : B → A) → id ∼ (g ∘ f) → isInjective f
-- hasRetract⇒isInjective = {!!}

sucIsInjective : isInjective Nat.suc
sucIsInjective x .x refl = refl

FinSucIsInjective : ∀ {n : ℕ} → isInjective (Fin.suc {n})
FinSucIsInjective x .x refl = refl

FinSucNatural : ∀ {n} (x : Fin n) → (suc (toℕ x) ≡ toℕ (suc x))
FinSucNatural x = refl

eqTrans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
eqTrans refl = id

eqSym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
eqSym refl = refl

toℕIsInjective : ∀ {n} → isInjective (toℕ {n})
toℕIsInjective {zero} ()
toℕIsInjective {suc n} zero zero p = refl
toℕIsInjective {suc n} zero (suc y) ()
toℕIsInjective {suc n} (suc x) zero ()
toℕIsInjective {suc n} (suc x) (suc y) p = cong suc subEq
  where
    subEq : x ≡ y
    subEq = toℕIsInjective x y (sucIsInjective (toℕ x) (toℕ y) p)

skip : {n : ℕ} → (skipNum : Fin (suc n)) → (x : Fin (suc n)) → ¬ (x ≡ skipNum) → Fin n
skip zero zero p₁ = ⊥-elim (p₁ refl)
skip zero (suc x) p₁ = x
skip {zero} (suc ())
skip {suc n₁} (suc skp) zero p₁ = zero {n₁}
skip {suc n₁} (suc skp) (suc x) p₁ = suc (skip {n₁} skp x (p₁ ∘ cong suc))

skipInj : ∀ {n : ℕ} (skp : Fin (suc n)) (x₁ x₂ : Fin (suc n)) →
          (neq₁ : ¬ (x₁ ≡ skp)) →
          (neq₂ : ¬ (x₂ ≡ skp)) →
          (skip skp x₁ neq₁ ≡ skip skp x₂ neq₂) →
          (x₁ ≡ x₂)
skipInj zero zero x₂ neq₁ neq₂ prf = ⊥-elim (neq₁ refl)
skipInj zero (suc x₁) zero neq₁ neq₂ prf = ⊥-elim (neq₂ refl)
skipInj zero (suc x₁) (suc x₂) neq₁ neq₂ prf = cong suc prf
skipInj (suc skp) zero zero neq₁ neq₂ prf = refl
skipInj (suc skp) zero (suc zero) neq₁ neq₂ ()
skipInj (suc skp) zero (suc (suc x₂)) neq₁ neq₂ ()
skipInj (suc skp) (suc zero) zero neq₁ neq₂ ()
skipInj (suc skp) (suc (suc x₁)) zero neq₁ neq₂ ()
skipInj {suc n} (suc skp) (suc x₁) (suc x₂) neq₁ neq₂ prf = cong suc $ prf′
  where
    neq₁′ = neq₁ ∘ cong suc
    neq₂′ = neq₂ ∘ cong suc
    y₁ = skip skp x₁ neq₁′
    y₂ = skip skp x₂ neq₂′
    prf′ = skipInj skp x₁ x₂ neq₁′ neq₂′ (FinSucIsInjective y₁ y₂ prf)

pigeonholePrinciple : ∀ (n m : ℕ)
                      → suc n Nat.≤ m
                      → (f : Fin (suc m) → Fin (suc n))
                      → Σ (Fin (suc m)) (collisionType (suc n) (suc m) f)
                      
pigeonholePrinciple n zero ()
pigeonholePrinciple zero (suc _) (s≤s prf) f = zero , (Fin.suc zero , 1≠0 , p)
  where
    1≠0 : (x : suc zero ≡ zero) → ⊥
    1≠0 ()
    p : f zero ≡ f (suc zero)
    p with f zero
    p | zero with f (suc zero)
    p | zero | zero = refl
    p | zero | suc ()
    p | suc ()
pigeonholePrinciple (suc n) (suc m-1) lt f with checkZeroCollision (suc m-1) (toℕ ∘ f)
pigeonholePrinciple (suc n) (suc m-1) lt f | yes (proj₁ , proj₂) = zero , (suc proj₁ , pf₁ , pf₂)
  where
    pf₁ : suc proj₁ ≡ zero → ⊥
    pf₁ ()
    pf₂ : f zero ≡ f (suc proj₁)
    pf₂ = eqSym (toℕIsInjective (f (suc proj₁)) (f zero) proj₂)
pigeonholePrinciple (suc n) (suc m-1) lt f | no p with pigeonholePrinciple n m-1 (cong* lt) f′
  where
    cong* : ∀ {x y : ℕ} → suc x Nat.≤ suc y → x Nat.≤ y
    cong* (s≤s lt₁) = lt₁
    f′ : Fin (suc m-1) → Fin (suc n)
    f′ x = skip (f zero) (f (suc x)) neq
      where
        neq : (x₁ : f (suc x) ≡ f zero) → ⊥
        neq eq = p (x , cong toℕ eq)
pigeonholePrinciple (suc n) (suc m-1) lt f | no p | proj₁ , proj₂ , proj₃ , proj₄ = prf
  where
    neq₁ : ¬ f (suc proj₁) ≡ f zero
    neq₁ eq = p (proj₁ , cong toℕ eq) 
    neq₂ : ¬ f (suc proj₂) ≡ f zero
    neq₂ eq = p (proj₂ , cong toℕ eq)
    prf = suc proj₁ ,
          suc proj₂ ,
          proj₃ ∘ FinSucIsInjective proj₂ proj₁ ,
          skipInj (f zero) (f (suc proj₁)) (f (suc proj₂)) neq₁ neq₂ proj₄
