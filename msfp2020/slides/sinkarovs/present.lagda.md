---
title: "Multi-dimensional Arrays with Levels"
subtitle: "MSFP 2020"
author: "Artjoms Šinkarovs"
date: "01 September 2020"

transition: "linear"
center: "false"
width: 1200
height: 800
margin: "0.2"
---

# Agenda

* Formalising arrays in a dependently-typed context
* Containers
  - discovering a new container operation
  - discovering array hierarchies
* Practical application


# Formalising Arrays



Key features we would like to have in the model:

* Rank polymorphism
* Static bounds checking
* Can represent any APL operator
* Extendable [optional]

# Formalising Arrays

Static bounds checking and the ability to encode operations
such as `take` or `drop` suggests that arrays should be
dependently-typed.

. . .

Here is a type for an $n$-dimensional array.

<!--
```agda
{-# OPTIONS --rewriting #-}
module _ where
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec using (Vec; []; _∷_; lookup; foldr)
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function
--infixr 5 _∷_


module _ where
```
-->
```agda
  data Ix : (d : ℕ) → (s : Vec ℕ d) → Set where
    []   : Ix 0 []
    _∷_  : ∀ {d s x} → Fin x → Ix d s → Ix (suc d) (x ∷ s)

  data Ar (X : Set) (d : ℕ) (s : Vec ℕ d) : Set where
    imap : (Ix d s → X) → Ar X d s
```


## Examples

<!--
```agda
--module _ where
  postulate
    sum : ∀ {n} → Ar ℕ 1 (n ∷ []) → ℕ

  Mat : ℕ → ℕ → Set
```
-->
Consider a straight-forward matrix transpose:
```agda
  Mat x y = Ar ℕ 2 (x ∷ y ∷ [])

  transpose : ∀ {a b} → Mat a b → Mat b a
  transpose (imap a) = imap body where
    body : _
    body (i ∷ j ∷ []) = a $ j ∷ i ∷ []
```

Matrix multiplication:
```
  mm : ∀ {a b c} → Mat a b → Mat b c → Mat a c
  mm (imap a) (imap b) = imap body where
    body : _
    body (i ∷ j ∷ []) = sum
      $ imap λ where (k ∷ []) → a (i ∷ k ∷ []) * b (k ∷ j ∷ [])
```


## Containers

```agda
  record Con : Set₁ where
    constructor _◃_
    field
      Sh : Set
      Po : Sh → Set
    ⟦_⟧◃  : Set → Set
    ⟦_⟧◃ X = Σ Sh λ s → Po s → X
```

<!--
```agda
  module hide where
    open Con public
    postulate
      _≅_ : Set → Set → Set
```
-->
```agda
    List : Set → Set
    List X = ⟦ ℕ ◃ Fin ⟧◃ X -- ≡ Σ ℕ λ n → Fin n → X
```

## Containers


>  `Ar` is nothing but a container.
>
>  -- Peter Hancock.

. . .

Let us rewrite an array as follows:

```agda
  -- Vec X n ≅ Fin n → X
  -- Ix d sh ≅ (i : Fin d) → Fin (lookup sh i)

  Ar₁ : Set → Set
  Ar₁ X = (d : ℕ) → (sh : Fin d → ℕ)
                  → (((i : Fin d) → Fin (sh i)) → X)
```

## Containers
After uncurrying first two arguments:
<!--
```agda
  open Con public
  infixl 2 _◃_
```
-->
```agda
  Ar₂ : Set → Set
  Ar₂ X = ⟦ (Σ ℕ λ d → Fin d → ℕ)
            ◃ (λ where (d , sh) → (i : Fin d) → Fin (sh i)) ⟧◃ X
```

After noticing that the first `Σ` is a container:
```agda
  Ar₃ : Set → Set
  Ar₃ X = ⟦ ⟦ ℕ ◃ Fin ⟧◃ ℕ
            ◃ (λ where (d , sh) → (i : Fin d) → Fin (sh i)) ⟧◃ X
```

## Containers

Finally, let us generalise this into a container operation:

```agda
  Π : (A : Set) → (A → Set) → Set
  Π A B = (i : A) → B i

  _⋄_ : Con → Con → Con
  (A ◃ B) ⋄ (C ◃ D) = ⟦ A ◃ B ⟧◃ C
                      ◃ λ { (a , γ) → Π (B a) (D ∘ γ) }
```
In this case, we can rewrite an array type as:

```agda
  Array : Set → Set
  Array X = ⟦ (ℕ ◃ Fin) ⋄ (ℕ ◃ Fin) ⟧◃ X
```


## The ⋄ operation

An intuitive explanation of the `_⋄_` can be seen through
the tensor product `_⊗_` on containers that is defined as:

```agda
  _⊗_ : Con → Con → Con
  (A ◃ B) ⊗ (C ◃ D) = (A × C) ◃ λ where (a , c) → B a × D c
```

Now assume that we want to compute an $n$-fold tensor product
of a container `C ◃ D`.  That is: `(C ◃ D) ⊗ (C ◃ D) ⊗ ⋯`.
In this case we can set "the boundaries" of the product using
`A ◃ B`.

$$
        (A ◃ B) ⋄ (C ◃ D) =
        ⨂_{(A ◃ B)} (C ◃ D)
$$

## The ⋄ operation

A nice analogy that we observe: tensor product "replaces" `+`
with `×` in:
<!--
```agda
  _×'_ _⊗'_ : Con → Con → Con
  _∘'_ _⋄'_ : Con → Con → Con

```
-->
```agda
  (A ◃ B) ×' (C ◃ D) = (A × C) ◃ λ where (a , c) → B a ⊎ D c
  (A ◃ B) ⊗' (C ◃ D) = (A × C) ◃ λ where (a , c) → B a × D c
```
In a similar way `⋄` replaces `Σ` with `Π` in:

```agda
  (A ◃ B) ∘' (C ◃ D) = ⟦ A ◃ B ⟧◃ C ◃ λ where (a , γ) → Σ (B a) (D ∘ γ)
  (A ◃ B) ⋄' (C ◃ D) = ⟦ A ◃ B ⟧◃ C ◃ λ where (a , γ) → Π (B a) (D ∘ γ)
```

# Array Hierarchy

As `_⋄_ : Con → Con → Con`, it can be iterated.
As `_⋄_` is not associative, iteration on the left and on the
right gives different results.

```agda
  1ₐ : Con
  1ₐ = ⊤ ◃ λ _ → ⊤

  AL : ℕ → Con
  AL 0 = 1ₐ
  AL (suc x) = (ℕ ◃ Fin) ⋄ (AL x)

  AR : ℕ → Con
  AR 0 = 1ₐ
  AR (suc x) = (AR x) ⋄ (ℕ ◃ Fin)
```

## Iterating ⋄ on the left (right assoc)

Iteration on the left makes the "counting container" more
complex.

```agda
  AL₃ : Set → Set
  AL₃ X = ⟦ (ℕ ◃ Fin) ⋄ ((ℕ ◃ Fin) ⋄ (ℕ ◃ Fin)) ⟧◃ X

  sanityₗ : ∀ X → AL₃ X
          ≡ Σ (⟦ ℕ ◃ Fin ⟧◃ (⟦ ℕ ◃ Fin ⟧◃ ℕ)) -- Vec of Vec of ℕ
              λ { (ss , ff)
                  → ((ii : Fin ss)
                      → let s , f = ff ii in
                         (i : Fin s) → Fin (f i)) → X}
  sanityₗ X = refl

  -- The shape of level-3 array becomes inhomogeneous, e.g:
  --     2
  --     3 4 5 6
  --     1 2
```


## Iterating ⋄ on the right (left assoc)


```agda
  AR₃ : Set → Set
  AR₃ X = ⟦ ((ℕ ◃ Fin) ⋄ (ℕ ◃ Fin)) ⋄ (ℕ ◃ Fin) ⟧◃ X

  sanityᵣ : ∀ X → AR₃ X
          ≡ Σ (⟦ (ℕ ◃ Fin) ⋄ (ℕ ◃ Fin) ⟧◃ ℕ)
              λ { ((d , s) , ss) -- ss is array of shape s of ℕ
                  → Π (Π (Fin d) (Fin ∘ s)) (Fin ∘ ss) → X}
  sanityᵣ X = refl
```

The shape of level-3 array is a level-2 array of `ℕ`


## `AR` hierarchy

By adopting `AR`, all the shapes (> level-0) are arrays themselves:

 Level    Shape          Array
 -------- -----------    -----------------------------
 level-0  `⊤`            "scalars" (0-dimensional)
 level-1  level-0 of ℕ    vectors (1-dimensional)
 level-2  level-1 of ℕ    multi-dimensional
 level-3  level-2 of ℕ    multi-multi-dimensional
 ...

. . .

Note: all of the higher-level arrays (> 1) can be mapped into
vectors (level 1).


# Practical use

Average pooling example using ranked operator (demo).

# Encoding

<!--
```agda
module encoding where
```
-->
```agda
  ShType : (l : ℕ) → Set
  IxType : (l : ℕ) → ShType l → Set
  ReprAr : ∀ l (X : Set) → Set

  record IxLvl (l : ℕ) (s : ShType l) : Set where
    constructor ix
    field flat-ix : IxType l s

  data ArLvl {a} (l : ℕ) (X : Set a) (s : ShType l) : Set a where
    imap : (IxLvl l s → X) → ArLvl l X s
```

# Encoding

```agda
  prod : ∀ {l} → ShType l → ℕ

  ShType zero    = ⊤
  ShType (suc l) = ReprAr l ℕ

  ReprAr l X = Σ (ShType l) λ s → Vec X (prod {l = l} s)

  IxType zero tt = ⊤
  IxType (suc l) (s , vec) = Ix (prod s) vec

  prod {zero}  sh = 1
  prod {suc l} (s , vec) = foldr _ _*_ 1 vec
```

# Conclusions

* Generalisation of multi-dimensional arrays
  - a hierarchy of array types with a very rich shape structure
  - level-polymorphic operations
* Discovered a novel container operation
* Formalisation in Agda
  - found encoding for the hierarchy
  - implemented key array operations, e.g. reshape, flatten, ranked, etc
  - average pooling using generalised ranked operator
  - available at GitHub
    [ashinkarov/agda-arrays-with-levels](https://github.com/ashinkarov/agda-arrays-with-levels)

. . .

Big thanks to Peter Hancock and Sven-Bodo Scholz for a number of
very productive discussions.
