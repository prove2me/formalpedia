-- Prove2me | solution 1 for TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:00:57.162786+00:00
-- url     : https://prove2.me/submissions/80cfcd21-7280-41a5-838e-5e8ad4302597

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_PowerIndex
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_IdealArithmeticFunction_summable_idealTerm_vonMangoldtTransform
import Theorems.Thm_TauCeti_MultiplicativeIdealWeight_logDeriv_LSeries_eq_tsum_prime_pow

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Regrouping an ideal-indexed Dirichlet series by absolute norm

An `TauCeti.IdealArithmeticFunction K` has two Dirichlet series attached to it: the series indexed
by the nonzero integral ideals of `𝓞 K`, whose terms are `TauCeti.idealTerm`, and the Mathlib
`LSeries` of the regrouped coefficients `TauCeti.normCoeff`. This file proves that the second is
obtained from the first by summing over the finite absolute-norm fibres, so that absolute
convergence of the ideal-indexed series transfers to the `LSeries` together with the value of the
sum.

## Main definitions

* `TauCeti.idealTerm f s I` is the term `f I / N(I) ^ s` of the ideal-indexed Dirichlet series.
* `TauCeti.idealAbscissaOfAbsConv f` is the abscissa of absolute convergence of that series, the
  ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`.

## Main results

* `TauCeti.regroupByNorm`: if the ideal-indexed series has sum `L` at `s`, then so does the
  `LSeries` of `TauCeti.normCoeff f`; `TauCeti.LSeriesSummable_normCoeff` and
  `TauCeti.LSeries_normCoeff` are the summability and value statements it packages.
* `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`: weighting the ideal terms
  by `log N(I)` keeps them summable strictly to the right of a point of absolute convergence.
* `TauCeti.abscissaOfAbsConv_normCoeff_le`: consequently the grouped abscissa of absolute
  convergence is at most the ideal-indexed one.
* `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm`: the converse holds whenever no
  cancellation occurs inside a norm fibre. `TauCeti.summable_idealTerm_of_nonneg` and
  `TauCeti.idealAbscissaOfAbsConv_eq_abscissaOfAbsConv` specialize it to the case where every
  *individual ideal summand* is nonnegative, where moreover the two abscissae agree.

## Implementation notes

The regrouping is an instance of Mathlib's `HasSum.tsum_fiberwise` along the absolute norm
`fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))`, whose fibres are the finite sets
`TauCeti.normFiber K n`. Absolute convergence of the ideal-indexed series is expressed as plain
`Summable`, which for a complex-valued family is unconditional convergence and hence absolute
convergence; no rearrangement hypothesis is therefore needed for the transfer.

The converse is proved through `summable_partition` applied to the norms of the terms. All it
needs about `f` is that the norm of each grouped coefficient is the sum of the norms over its
fibre — the absence of cancellation inside the fibre. Nonnegativity of every ideal summand is one
way to secure that, through `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`; it is the step that
fails under cancellation, as the rejection test
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` records. That test is a statement about
`TauCeti.normCoeff` alone, so it lives with that definition rather than here.

## Roadmap role

This is Layer **1.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the required worked
example 9 accompanies it in `TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean`. The
exact value of the abscissa for the trivial weight is deliberately not proved here: its divergence
input is the Layer 5 ideal count of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti

open scoped _root_.nonZeroDivisors _root_.NumberField _root_.ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/



/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)











/-! ### Regrouping -/











/-! ### The ideal-indexed abscissa of absolute convergence -/













/-! ### The converse, in the absence of cancellation inside norm fibres -/











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
# Indexing the prime-power ideals by a prime and an exponent

Every prime-power ideal of `𝓞 K` is `𝔭 ^ (k + 1)` for a unique height-one prime `𝔭` and a unique
`k : ℕ`. This file records that bijection and what it does to an infinite sum: a *summable* family
on the prime-power ideals has the same sum as the iterated sum over primes and exponents, and a
*summable* family on *all* nonzero ideals collapses to that same iterated sum whenever it is
supported on prime powers. Both statements assume summability; neither asserts it.

This is the ideal analogue of Mathlib's `Nat.Primes.prodNatEquiv` and the two summation lemmas
built on it, `tsum_primes_pow_eq` and `tsum_eq_tsum_primes_of_support_subset_prime_powers`. Those
are what turns an Euler-product logarithm, which is naturally indexed by `(𝔭, k)`, into a Dirichlet
series indexed by ideals — the shape a von Mangoldt coefficient identity needs.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.idealPrimePowerOf`: the prime-power ideal `𝔭 ^ (k + 1)`.
* `TauCeti.idealPrimePowerEquiv`: the bijection `(𝔭, k) ↦ 𝔭 ^ (k + 1)` onto the prime-power ideals.

## Main results

* `TauCeti.summable_comp_idealPrimePowerOf`: a summable family on all nonzero ideals remains
  summable after restriction to the positive prime powers.
* `TauCeti.summable_tsum_norm_idealPrimePowerOf`: the prime-power tails of an absolutely
  summable ideal-indexed family are summable over the primes.
* `TauCeti.tsum_idealPrimePower_eq`: a summable family on the prime-power ideals has the same sum
  as the iterated sum over primes and exponents.
* `TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`: a summable family on the nonzero
  ideals supported on prime powers has the same sum as that iterated sum.

## Implementation notes

The inverse sends `A` to `(primePowerBase A, primePowerExponent A - 1)`. The truncated subtraction
is harmless because `primePowerExponent A` is positive, and the `+ 1` in the forward map is what
keeps the exponent positive without carrying a hypothesis.
-/

 section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField TauCeti

variable {K : Type*} [Field K] [NumberField K]

namespace IsDedekindDomain.HeightOneSpectrum











end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



end TauCeti

namespace IsDedekindDomain.HeightOneSpectrum

@[simp]
theorem idealPrimePowerEquiv_apply (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    idealPrimePowerEquiv (P, k) = P.idealPrimePowerOf k :=
  (rfl)

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



variable {α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α]
  {f : (Ideal (𝓞 K))⁰ → α}



section Norm

variable {β : Type*} [NormedAddCommGroup β] {g : (Ideal (𝓞 K))⁰ → β}



end Norm

variable [T0Space α]

/-- **Summing over prime-power ideals is summing over primes and exponents.**  Stated for an
arbitrary family on the prime-power ideals, not only for one restricted from the nonzero
ideals. -/
theorem tsum_idealPrimePower_eq {g : IdealPrimePower K → α} (hg : Summable g) :
    ∑' (P : HeightOneSpectrum (𝓞 K)) (k : ℕ), g (P.idealPrimePowerOf k)
      = ∑' A : IdealPrimePower K, g A := calc
  _ = ∑' Pk : HeightOneSpectrum (𝓞 K) × ℕ, g (idealPrimePowerEquiv Pk) := by
    simpa using (hg.comp_injective idealPrimePowerEquiv.injective).tsum_prod.symm
  _ = _ := by rw [← Equiv.tsum_eq idealPrimePowerEquiv]

/-- **A sum supported on prime powers is a sum over primes and exponents.** -/
theorem tsum_eq_tsum_idealPrimePower_of_support_subset (hfm : Summable f)
    (hf : Function.support f ⊆ {A : (Ideal (𝓞 K))⁰ | IsPrimePow (A : Ideal (𝓞 K))}) :
    ∑' A : (Ideal (𝓞 K))⁰, f A
      = ∑' (P : HeightOneSpectrum (𝓞 K)) (k : ℕ),
          f (P.idealPrimePowerOf k : (Ideal (𝓞 K))⁰) := by
  rw [tsum_idealPrimePower_eq (g := fun A : IdealPrimePower K ↦ f A.1) (hfm.subtype _)]
  exact (tsum_subtype_eq_of_support_subset hf).symm

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
# The ideal von Mangoldt function

The von Mangoldt function of a nonzero ideal `A` of the ring of integers of a number field is
`log N(P)` when `A` is a positive power of a prime ideal `P`, and zero otherwise.  This file
packages that function as an `IdealArithmeticFunction` and defines its pointwise product with an
ideal arithmetic function.

## Main definitions

* `TauCeti.IdealArithmeticFunction.vonMangoldt` is the complex-valued ideal von Mangoldt
  function.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform` sends `f` to the weighted function
  `A ↦ f(A) Λ(A)`.

## Main results

* `TauCeti.IdealArithmeticFunction.vonMangoldt_apply_prime_pow` computes the value on a positive
  power of a prime ideal.
* `TauCeti.IdealArithmeticFunction.vonMangoldt_ne_zero_iff` says that its support is exactly the
  prime-power ideals.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff` identifies the support of
  the transform, and its specialization in `TauCeti.MultiplicativeIdealWeight` describes this as
  the good prime powers for a completely multiplicative weight.

The definition chooses a prime base from a proof that `A` is a prime power.  Mathlib's
`eq_of_prime_pow_eq`, applied to ideals, identifies that choice with any prime base supplied by a
caller.  The public evaluation theorem therefore removes the choice from every computation.

## Implementation notes

This is the ideal analogue of Mathlib's `ArithmeticFunction.vonMangoldt`.  Here the prime base is
chosen from `IsPrimePow` rather than computed by `Nat.minFac`, its logarithmic weight is
`Ideal.absNorm P` rather than `p`, and the function is complex-valued to match
`IdealArithmeticFunction`.

## Roadmap role

This is the algebraic part of Layer **2.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The logarithmic-derivative identity named in
that target additionally requires the Euler-product package of Layer 3; this file supplies its
coefficient and exact prime-power support in advance.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

 section

namespace TauCeti

open _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of a prime ideal is greater than one. -/
theorem one_lt_absNorm_of_prime {P : Ideal (𝓞 K)} (hP : Prime P) :
    1 < Ideal.absNorm P := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero,
    Ideal.absNorm_eq_one_iff.not.mpr fun htop ↦
      hP.not_isUnit (Ideal.isUnit_iff.mpr htop)⟩

namespace IdealArithmeticFunction





/-- The value of the ideal von Mangoldt function at a positive power of a prime ideal.  This is the
choice-free characterization of `vonMangoldt` on its support. -/
theorem vonMangoldt_apply_of_eq_prime_pow {A : (Ideal (𝓞 K))⁰} {P : Ideal (𝓞 K)}
    (hP : Prime P) {n : ℕ} (hn : 0 < n) (hpow : P ^ n = (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = Real.log (Ideal.absNorm P) := by
  have hA : IsPrimePow (A : Ideal (𝓞 K)) := ⟨P, n, hP, hn, hpow⟩
  have hchosen : hA.choose = P := by
    exact eq_of_prime_pow_eq hA.choose_spec.choose_spec.1 hP
      hA.choose_spec.choose_spec.2.1 (hA.choose_spec.choose_spec.2.2.trans hpow.symm)
  rw [vonMangoldt, dif_pos hA, hchosen]

/-- The ideal von Mangoldt function at a positive power of a prime nonzero ideal. -/
@[simp]
theorem vonMangoldt_apply_prime_pow {P : (Ideal (𝓞 K))⁰}
    (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    (vonMangoldt : IdealArithmeticFunction K) (P ^ n) =
      Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  apply vonMangoldt_apply_of_eq_prime_pow hP hn
  simp



/-- The ideal von Mangoldt function vanishes away from prime powers. -/
@[simp]
theorem vonMangoldt_eq_zero_of_not_isPrimePow {A : (Ideal (𝓞 K))⁰}
    (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 := by
  simp [vonMangoldt, hA]

/-- The support of the ideal von Mangoldt function is exactly the set of prime-power ideals. -/
theorem vonMangoldt_ne_zero_iff {A : (Ideal (𝓞 K))⁰} :
    (vonMangoldt : IdealArithmeticFunction K) A ≠ 0 ↔ IsPrimePow (A : Ideal (𝓞 K)) := by
  constructor
  · intro hne
    by_contra hnot
    exact hne (vonMangoldt_eq_zero_of_not_isPrimePow hnot)
  · rintro ⟨P, n, hP, hn, hpow⟩
    rw [vonMangoldt_apply_of_eq_prime_pow hP hn hpow]
    apply Complex.ofReal_ne_zero.mpr
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm_of_prime hP)
    · exact_mod_cast (one_lt_absNorm_of_prime hP).ne'













/-- Evaluation of the von Mangoldt transform. -/
theorem vonMangoldtTransform_apply (f : IdealArithmeticFunction K)
    (A : (Ideal (𝓞 K))⁰) :
    f.vonMangoldtTransform A = f A * vonMangoldt A := by
  rw [vonMangoldtTransform, Pi.mul_apply]

/-- The von Mangoldt transform on a positive power of a prime ideal. -/
@[simp]
theorem vonMangoldtTransform_apply_prime_pow (f : IdealArithmeticFunction K)
    {P : (Ideal (𝓞 K))⁰} (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    f.vonMangoldtTransform (P ^ n) =
      f (P ^ n) * Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  rw [vonMangoldtTransform_apply, vonMangoldt_apply_prime_pow hP hn]

/-- The support of a von Mangoldt transform is the intersection of the support of the original
function with the prime-power ideals. -/
@[simp]
theorem vonMangoldtTransform_ne_zero_iff (f : IdealArithmeticFunction K)
    {A : (Ideal (𝓞 K))⁰} :
    f.vonMangoldtTransform A ≠ 0 ↔
      IsPrimePow (A : Ideal (𝓞 K)) ∧ f A ≠ 0 := by
  rw [vonMangoldtTransform_apply, mul_ne_zero_iff, vonMangoldt_ne_zero_iff, and_comm]



end IdealArithmeticFunction

namespace MultiplicativeIdealWeight

/-- The von Mangoldt transform of a completely multiplicative weight on a positive power of a
prime ideal. -/
theorem vonMangoldtTransform_apply_prime_pow (χ : MultiplicativeIdealWeight K)
    {P : (Ideal (𝓞 K))⁰} (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    χ.toIdealArithmeticFunction.vonMangoldtTransform (P ^ n) =
      χ P ^ n * Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  rw [IdealArithmeticFunction.vonMangoldtTransform_apply_prime_pow _ hP hn,
    toIdealArithmeticFunction_apply]
  rw [SubmonoidClass.coe_pow, map_pow]



end MultiplicativeIdealWeight

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
# The logarithmic derivative as a von Mangoldt Dirichlet series

Strictly to the right of the abscissa of absolute convergence,

`logDeriv L(s) = -∑' A, χ(A) Λ(A) / N(A) ^ s`,

the sum running over the nonzero integral ideals of `𝓞 K`, with `Λ` the ideal von Mangoldt
function. This is the coefficient identity: it names the exact Dirichlet coefficients of the
logarithmic derivative, which is what a Tauberian argument consumes.

The prime-power expansion of `logDeriv_LSeries_eq_tsum_prime_pow` is the same sum written over
`(𝔭, k)`. The two agree termwise, because the von Mangoldt transform of a completely multiplicative
weight at `𝔭 ^ (k+1)` is `χ(𝔭) ^ (k+1) log N(𝔭)` and `N(𝔭 ^ (k+1)) = N(𝔭) ^ (k+1)`; the transform
vanishes off the prime powers, so nothing else contributes.

For general Euler-product data `D`, whose values at higher prime powers are independent, the
coefficient at `𝔭 ^ e` is `log N(𝔭)` times the degree-`e` coefficient of the local series
`X F_𝔭'/F_𝔭`. This defines the von Mangoldt function `Λ_D` of `D`, which is the von Mangoldt
transform of the weight in the completely multiplicative case. Where the local power series are
zero-free on the disks of absolute convergence, `-logDeriv L(s) = ∑' A, Λ_D(A) / N(A) ^ s`, with
absolute convergence.

## Main definitions

* `TauCeti.EulerProductData.vonMangoldt`: the von Mangoldt function `Λ_D` of Euler-product data.

## Main results

* `TauCeti.IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform`: the von Mangoldt
  weighted ideal terms are summable on the half-plane, for any ideal arithmetic function.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform`: the
  coefficient identity for a completely multiplicative weight.
* `TauCeti.EulerProductData.vonMangoldt_ofMultiplicativeIdealWeight`: `Λ_D` of a completely
  multiplicative weight is its von Mangoldt transform.
* `TauCeti.EulerProductData.hasSum_idealTerm_vonMangoldt_of_zeroFree` and
  `TauCeti.EulerProductData.LSeriesHasSum_normCoeff_vonMangoldt_of_zeroFree`: the coefficient
  identity for general Euler-product data, ideal-indexed and regrouped by norm.

## Implementation notes

Summability is comparison against `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`,
whose weight `log N(I)` dominates `‖Λ(I)‖` by `norm_vonMangoldt_le_log`. Passing from the
`(𝔭, k)`-indexed sum to the ideal-indexed one is
`TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`.

For general `D`, `PowerSeries.tsum_norm_coeff_logDeriv_mul_pow_succ_le` supplies the local
majorant that gives absolute convergence of the von Mangoldt series. The general coefficient
identity applies to data with an absolute-convergence point `σ` and zero-free local series on the
corresponding disks.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1, for the von Mangoldt function of
  a general Euler product.
-/

 section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]



end IdealArithmeticFunction

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

/-- The von Mangoldt weighted ideal term at `𝔭 ^ (k + 1)` is the `(𝔭, k)` summand of the
prime-power expansion of the logarithmic derivative. -/
private theorem TauCeti.MultiplicativeIdealWeight.idealTerm_vonMangoldtTransform_prime_pow (s : ℂ)
    (P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    _root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s
        (P.idealPrimePowerOf k : (_root_.Ideal (𝓞 K))⁰)
      = _root_.Complex.log (_root_.Ideal.absNorm P.asIdeal : ℂ)
          * (χ P.asIdeal / (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ (k + 1) := by
  have hmem : P.asIdeal ∈ (_root_.Ideal (𝓞 K))⁰ := _root_.mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have hP : _root_.Prime (((⟨P.asIdeal, hmem⟩ : (_root_.Ideal (𝓞 K))⁰)) : _root_.Ideal (𝓞 K)) :=
    _root_.Ideal.prime_of_isPrime P.ne_bot P.isPrime
  have hpow : (P.idealPrimePowerOf k : (_root_.Ideal (𝓞 K))⁰)
      = (⟨P.asIdeal, hmem⟩ : (_root_.Ideal (𝓞 K))⁰) ^ (k + 1) := _root_.Subtype.ext (by simp)
  have hlog : _root_.Complex.log (_root_.Ideal.absNorm P.asIdeal : ℂ)
      = ((_root_.Real.log (_root_.Ideal.absNorm P.asIdeal) : ℝ) : ℂ) := by
    rw [← _root_.Complex.ofReal_natCast, ← _root_.Complex.ofReal_log (_root_.Nat.cast_nonneg _)]
  rw [_root_.TauCeti.idealTerm_def, hpow,
    _root_.TauCeti.MultiplicativeIdealWeight.vonMangoldtTransform_apply_prime_pow _ hP k.succ_pos,
    _root_.SubmonoidClass.coe_pow, _root_.map_pow, _root_.Nat.cast_pow, ← _root_.Complex.natCast_cpow_natCast_mul,
    _root_.Complex.cpow_nat_mul, _root_.div_pow, hlog, _root_.Nat.succ_eq_add_one]
  ring


/-- **The coefficient identity for the logarithmic derivative.** Strictly to the right of the
abscissa of absolute convergence,

`logDeriv L(s) = -∑' A, χ(A) Λ(A) / N(A) ^ s`.

The minus sign is the usual one: the Dirichlet coefficients of `-L'/L` are the von Mangoldt
transform of the weight, nonnegative when the weight is trivial. -/
theorem solution {s : ℂ}
    (hs : _root_.TauCeti.idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    _root_.logDeriv (_root_.LSeries (_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction)) s
      = -∑' A : (_root_.Ideal (𝓞 K))⁰,
          _root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s A := by
  have hsum := _root_.TauCeti.IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform
    (f := χ.toIdealArithmeticFunction) hs
  have hsupp : _root_.Function.support (_root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s)
      ⊆ {A : (_root_.Ideal (𝓞 K))⁰ | IsPrimePow (A : _root_.Ideal (𝓞 K))} := by
    intro A hA
    rw [_root_.Function.mem_support, _root_.TauCeti.idealTerm_def, _root_.div_ne_zero_iff] at hA
    exact ((_root_.TauCeti.IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff _).mp hA.1).1
  have hcoe : ∀ pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
      (pe.1.idealPrimePowerOf pe.2 : (_root_.Ideal (𝓞 K))⁰)
        = ((_root_.TauCeti.idealPrimePowerEquiv pe : _root_.TauCeti.IdealPrimePower K) : (_root_.Ideal (𝓞 K))⁰) := by
    rintro ⟨P, k⟩
    rw [_root_.IsDedekindDomain.HeightOneSpectrum.idealPrimePowerEquiv_apply]
  have hinj : _root_.Function.Injective
      (fun pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ ↦ (pe.1.idealPrimePowerOf pe.2 : (_root_.Ideal (𝓞 K))⁰)) :=
    fun a b hab ↦ idealPrimePowerEquiv.injective
      (_root_.Subtype.coe_injective ((hcoe a).symm.trans (hab.trans (hcoe b))))
  have key : ∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
      _root_.Complex.log (_root_.Ideal.absNorm pe.1.asIdeal : ℂ)
        * (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1)
      = ∑' A : (_root_.Ideal (𝓞 K))⁰,
          _root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s A := by
    have hprod := (hsum.comp_injective hinj).tsum_prod
    simp only [_root_.Function.comp_apply] at hprod
    rw [_root_.TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset hsum hsupp, ← hprod]
    exact _root_.tsum_congr fun pe ↦ (_root_.TauCeti.MultiplicativeIdealWeight.idealTerm_vonMangoldtTransform_prime_pow χ s pe.1 pe.2).symm
  rw [χ.logDeriv_LSeries_eq_tsum_prime_pow hs, _root_.tsum_neg, key]

end MultiplicativeIdealWeight

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

variable {K : Type*} [Field K] [NumberField K] (D : EulerProductData K)









section Analytic

variable {σ : ℝ} {s : ℂ}















end Analytic

end EulerProductData

end TauCeti

end
end
