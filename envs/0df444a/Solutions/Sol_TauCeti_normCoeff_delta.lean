-- Prove2me | solution 1 for TauCeti.normCoeff_delta
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:12.0156+00:00
-- url     : https://prove2.me/submissions/35dc458f-2e9c-40aa-a70f-ec79e03050c3

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Convolution
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API exposes the finite norm fibre
`TauCeti.normFiber` and its finiteness, records the value at one, proves compatibility with
complex conjugation, and records in `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg` that no
cancellation occurs inside a fibre when the values of `f` are nonnegative.  Regrouping is
compatible with transporting along an isomorphism of number fields: `TauCeti.normCoeff_map` says
that an isomorphism `e : K ≃+* L` leaves every norm coefficient unchanged.

Regrouping loses information as soon as a norm fibre has more than one element:
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` produces a nonzero ideal arithmetic
function, with a negative value, whose norm coefficients all vanish.  This is the rejection test
that forbids weakening the nonnegativity hypothesis of the converse regrouping theorem to
nonnegativity of the coefficients themselves.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next layer step uses these coefficients
to regroup an absolutely convergent series over nonzero ideals into a Mathlib `LSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]











/-- The unit ideal is the unique nonzero integral ideal of absolute norm one. -/
@[simp]
theorem normFiber_one : normFiber K 1 = {1} := by
  ext I
  simp [Ideal.absNorm_eq_one_iff, Subtype.ext_iff]



/-- The value of `normCoeff f` is the finite sum of `f` over the corresponding absolute-norm
fibre. -/
theorem normCoeff_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I :=
  (rfl)

/-- The value of `normCoeff f` as a sum over the finite absolute-norm fibre. -/
theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [normFiber]



/-- The norm coefficient at `1` is the value at the unit ideal. -/
@[simp]
theorem normCoeff_apply_one (f : IdealArithmeticFunction K) : normCoeff K f 1 = f 1 := by
  rw [normCoeff_eq_sum_normFiber, normFiber_one]
  simp











/-! ### The cancellation rejection test -/



end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ideal convolution of ideal arithmetic functions

The Dirichlet convolution of two arithmetic functions on the nonzero ideals of the ring of integers
of a number field `K` sums over the factorizations `B * C = A` of a nonzero ideal `A`. This file
constructs that index set, defines the convolution, and proves that it makes
`TauCeti.IdealArithmeticFunction K` a commutative monoid with identity
`TauCeti.IdealArithmeticFunction.delta`, bilinear over the pointwise additive structure.
It also transports this operation through `TauCeti.normCoeff` to Mathlib's Dirichlet convolution
on `ArithmeticFunction ℂ`.

## Main definitions

* `TauCeti.IdealArithmeticFunction.delta` is the ideal arithmetic function that is `1` at the unit
  ideal and `0` elsewhere.
* `TauCeti.Ideal.divisorsAntidiagonal A` is the finite set of pairs `(B, C)` of nonzero ideals with
  `B * C = A`; it is the ideal analogue of Mathlib's `Nat.divisorsAntidiagonal`.
* `TauCeti.IdealArithmeticFunction.convolution f g` is the ideal Dirichlet convolution.
* `TauCeti.IdealArithmeticFunction.convolutionPow f n` is the `n`-fold convolution power of `f`.

## Main results

* `TauCeti.IdealArithmeticFunction.convolution_comm`,
  `TauCeti.IdealArithmeticFunction.convolution_assoc`,
  `TauCeti.IdealArithmeticFunction.delta_convolution` and
  `TauCeti.IdealArithmeticFunction.convolution_delta`: the convolution monoid laws.
* `TauCeti.IdealArithmeticFunction.convolution_add` and
  `TauCeti.IdealArithmeticFunction.add_convolution`: bilinearity over pointwise addition.
* `TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul`: ideal convolution is not the
  pointwise product.
* `TauCeti.normCoeff_delta`, `TauCeti.normCoeff_convolution`, and
  `TauCeti.normCoeff_convolutionPow`: regrouping by absolute norm transports the convolution
  identity, convolution, and convolution powers to Mathlib arithmetic functions.

## Implementation notes

`TauCeti.IdealArithmeticFunction K` is a `Pi` type, so it already carries Mathlib's *pointwise*
`CommRing` structure, in which `f * g` is `fun A => f A * g A` and `1` is the everywhere-one
function. Convolution is therefore deliberately **not** registered as a `Mul` instance and its
identity is the separate function `TauCeti.IdealArithmeticFunction.delta`; this is the roadmap's
convention that pointwise multiplication and ideal convolution stay distinct operations on one
carrier. The monoid laws are stated as ordinary theorems about
`TauCeti.IdealArithmeticFunction.convolution`, and
`TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul` records that the two products really do
differ. Consequently iterated convolution is the explicit
`TauCeti.IdealArithmeticFunction.convolutionPow` rather than a `Monoid.npow`.

Excluding the zero ideal from the carrier is what makes the index set finite: `⊥ * J = ⊥` for every
`J`, so the zero ideal has infinitely many factorizations while a nonzero ideal has only finitely
many, by Mathlib's `UniqueFactorizationMonoid.fintypeSubtypeDvd` for the unique factorization
monoid `Ideal (𝓞 K)`.

## Roadmap role

This is Layer **2.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, built on the Layer
**0.1** carrier of `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`. Its consumers are
the ideal Möbius function and von Mangoldt transform of Layer 2 and the local factors of Layer 3.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open scoped nonZeroDivisors NumberField

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K]

/-! ### The convolution identity -/



/-- The delta function takes the value `1` at the unit ideal. -/
@[simp]
theorem TauCeti.IdealArithmeticFunction.delta_one : _root_.TauCeti.IdealArithmeticFunction.delta (1 : (_root_.Ideal (𝓞 K))⁰) = 1 := by
  simp [_root_.TauCeti.IdealArithmeticFunction.delta]

/-- The delta function vanishes away from the unit ideal. -/
@[simp]
theorem TauCeti.IdealArithmeticFunction.delta_of_ne_one {A : (_root_.Ideal (𝓞 K))⁰} (hA : A ≠ 1) : _root_.TauCeti.IdealArithmeticFunction.delta A = 0 := by
  simp [_root_.TauCeti.IdealArithmeticFunction.delta, hA]



end IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.Ideal
end TauCeti.Ideal
section Ideal
open TauCeti TauCeti.Ideal

/-! ### The antidiagonal of a nonzero ideal -/

















end Ideal

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

/-! ### Ideal convolution -/







/-! ### The monoid laws -/









/-! ### Bilinearity over the pointwise additive structure -/





















/-! ### Iterated convolution -/













/-! ### Convolution is not the pointwise product -/





end IdealArithmeticFunction

/-! ## Compatibility with Dirichlet convolution -/

variable (K : Type*) [Field K] [NumberField K]

/-- Regrouping sends the identity for ideal convolution to the identity for Mathlib's Dirichlet
convolution. -/
@[simp]
theorem solution : _root_.TauCeti.normCoeff K _root_.TauCeti.IdealArithmeticFunction.delta = 1 := by
  classical
  ext n
  by_cases hn : n = 1
  · subst n
    rw [_root_.TauCeti.normCoeff_apply_one, _root_.TauCeti.IdealArithmeticFunction.delta_one]
    simp
  · simp only [_root_.TauCeti.normCoeff_eq_sum_normFiber, _root_.ArithmeticFunction.one_apply, hn]
    apply _root_.Finset.sum_eq_zero
    intro I hI
    apply _root_.TauCeti.IdealArithmeticFunction.delta_of_ne_one
    intro hI_one
    subst I
    have hnorm := (_root_.TauCeti.mem_normFiber K).mp hI
    exact hn (by simpa using hnorm.symm)





end TauCeti

end
end
