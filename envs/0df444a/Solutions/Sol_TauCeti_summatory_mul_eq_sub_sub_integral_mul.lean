-- Prove2me | solution 1 for TauCeti.summatory_mul_eq_sub_sub_integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:27:29.088069+00:00
-- url     : https://prove2.me/submissions/8495c221-6a7e-4a7c-97e0-6b194f2588b0

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_AbelSummation
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. The carrier depends only
on the integer part of the cutoff, and for a nonnegative cutoff it agrees with the one selected by
its natural floor.
-/

 section

namespace TauCeti

open Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]





/-- An index belongs to `normLE N x` exactly when its `N`-value is at most the inclusive
real cutoff `x`. -/
@[simp, grind =]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]

















/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]





























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
# Abel summation for norm-indexed summatory functions

Mathlib's `sum_mul_eq_sub_sub_integral_mul` is Abel summation for a sequence indexed by the natural
numbers.  Every counting argument of the arithmetic-Dirichlet-series roadmap instead sums a weight
over a carrier indexed by ideals or by height-one primes, cut off inclusively by the absolute norm.
This file supplies the bridge: the weight is regrouped into its norm fibres, Mathlib's identity is
applied to the resulting sequence, and the answer is read back as an equation between
`TauCeti.summatory` functions.

The bridge is stated for a general Northcott index `N : ι → ℕ`, because Layer 6 uses it for both
the ideal carrier and the prime carrier.  The integral runs over the half-open interval `Set.Ioc`,
so each boundary term is counted exactly once, as the roadmap's conventions table demands.

## Main results

* `TauCeti.summatory_mul_eq_sub_sub_integral_mul`: Abel summation between two nonnegative real
  cutoffs for a weight of the form `i ↦ w i * g (N i)`.
* `TauCeti.summatory_mul_eq_sub_integral_mul_of_le`: Abel summation from a real lower bound.
* `TauCeti.idealSummatory_mul_eq_sub_integral_mul`: the cutoff-`1` form for nonzero ideals.
* `TauCeti.primeSummatory_mul_eq_sub_integral_mul`: the cutoff-`2` form for the height-one primes
  of a number field.
* `TauCeti.norm_summatory_mul_cpow_le_of_summatory_le`: an imaginary-power twist preserves a
  positive power bound for partial sums, with an explicit constant.
* `TauCeti.integrableOn_mul_summatory`: a summatory function times an integrable factor is
  integrable on a compact interval, so the integrals above are genuine.
* `TauCeti.summatory_mul_le_of_summatory_le` and `TauCeti.tsum_mul_le_of_summatory_le`: for a
  nonnegative nonincreasing `g` and a carrier whose indices all have `N`-value at least `a ≥ 0`,
  an upper bound `C` on the partial sums of `w` gives the upper bound `C * g a` for the twisted
  partial sums and series.  This is how an eventual comparison of
  counting functions becomes a comparison of Dirichlet series uniform in `s`.
* `TauCeti.primeTheta_eq_log_mul_primeCount_sub_integral` and
  `TauCeti.primeCount_eq_primeTheta_div_log_add_integral`: the two exact Abel identities relating
  the roadmap's weighted prime counts,
  `ϑ(x) = π(x) log x - ∫_2^x π(t)/t dt` and `π(x) = ϑ(x)/log x + ∫_2^x ϑ(t)/(t log²t) dt`.
  Both hold for every real cutoff; below `2` all three terms vanish.

## Roadmap role

This is Layer **6.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: Mathlib's exact
finite identity is consumed, not restated, and only the norm-indexed bridges are added.  The two
prime identities are the finite input to Layer 6.2, which turns `ϑ(x) ∼ δx` into `π(x) ∼ δ Li(x)`
by estimating the integrals appearing here.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {ι : Type*} (N : ι → ℕ) [Northcott N] {𝕜 : Type*} [RCLike 𝕜]

/-! ### Regrouping a weight into its norm fibres -/



private theorem TauCeti.normFiberSum_eq_sum_filter (w : ι → 𝕜) (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    _root_.TauCeti.normFiberSum N w n = ∑ i ∈ _root_.TauCeti.normLE N x with N i = n, w i := by
  refine _root_.Finset.sum_congr ?_ fun _ _ ↦ _root_.rfl
  ext i
  simp only [_root_.Finset.mem_filter, _root_.TauCeti.mem_normLE, _root_.and_congr_left_iff]
  rintro rfl
  simp [hx]

private theorem TauCeti.normFiberSum_mul (w : ι → 𝕜) (g : ℝ → 𝕜) (n : ℕ) :
    _root_.TauCeti.normFiberSum N (fun i ↦ w i * g (N i)) n = g n * _root_.TauCeti.normFiberSum N w n := by
  simp only [_root_.TauCeti.normFiberSum, _root_.Finset.mul_sum]
  refine _root_.Finset.sum_congr _root_.rfl fun i hi ↦ ?_
  rw [(Finset.mem_filter.mp hi).2, _root_.mul_comm]

/-- A summatory function is the partial sum of the sequence of fibre sums. -/
private theorem TauCeti.summatory_eq_sum_Icc_normFiberSum (w : ι → 𝕜) {x : ℝ} (hx : 0 ≤ x) :
    _root_.TauCeti.summatory N w x = ∑ n ∈ _root_.Finset.Icc 0 ⌊x⌋₊, _root_.TauCeti.normFiberSum N w n := by
  have hmaps : ∀ i ∈ _root_.TauCeti.normLE N x, N i ∈ _root_.Finset.Icc 0 ⌊x⌋₊ := fun i hi ↦
    Finset.mem_Icc.mpr ⟨_root_.Nat.zero_le _, _root_.Nat.le_floor ((_root_.TauCeti.mem_normLE N).mp hi)⟩
  rw [_root_.TauCeti.summatory_apply, ← _root_.Finset.sum_fiberwise_of_maps_to hmaps w]
  refine _root_.Finset.sum_congr _root_.rfl fun n hn ↦ ?_
  exact (_root_.TauCeti.normFiberSum_eq_sum_filter N w n
    (_root_.le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (_root_.Nat.floor_le hx))).symm

private theorem TauCeti.sum_Ioc_normFiberSum (w : ι → 𝕜) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ _root_.Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, _root_.TauCeti.normFiberSum N w n = _root_.TauCeti.summatory N w b - _root_.TauCeti.summatory N w a := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := _root_.Nat.floor_le_floor hab
  have hdisj : _root_.Disjoint (_root_.Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) (_root_.Finset.Icc 0 ⌊a⌋₊) := by
    refine Finset.disjoint_left.mpr fun n hn hn' ↦ ?_
    simp only [_root_.Finset.mem_Ioc] at hn
    simp only [_root_.Finset.mem_Icc] at hn'
    omega
  have hunion : _root_.Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ∪ _root_.Finset.Icc 0 ⌊a⌋₊ = _root_.Finset.Icc 0 ⌊b⌋₊ := by
    ext n
    simp only [_root_.Finset.mem_union, _root_.Finset.mem_Ioc, _root_.Finset.mem_Icc]
    omega
  rw [_root_.TauCeti.summatory_eq_sum_Icc_normFiberSum N w (ha.trans hab),
    _root_.TauCeti.summatory_eq_sum_Icc_normFiberSum N w ha, _root_.eq_sub_iff_add_eq, ← _root_.Finset.sum_union hdisj, hunion]

/-! ### Abel summation over a Northcott carrier -/

/-- **Abel summation for a norm-indexed summatory function.**  For a weight `w` on the index type
and a function `g` differentiable on `[a, b]`, the summatory function of the twisted weight
`i ↦ w i * g (N i)` between the inclusive cutoffs `a` and `b` is the boundary term
`g b · A(b) - g a · A(a)` minus the integral of `g' · A`, where `A = summatory N w`.

This is Mathlib's `sum_mul_eq_sub_sub_integral_mul` read through the norm fibres of `N`. -/
theorem solution (w : ι → 𝕜) {g : ℝ → 𝕜} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hg_diff : ∀ t ∈ _root_.Set.Icc a b, _root_.DifferentiableAt ℝ g t)
    (hg_int : _root_.MeasureTheory.IntegrableOn (_root_.deriv g) (_root_.Set.Icc a b)) :
    _root_.TauCeti.summatory N (fun i ↦ w i * g (N i)) b - _root_.TauCeti.summatory N (fun i ↦ w i * g (N i)) a =
      g b * _root_.TauCeti.summatory N w b - g a * _root_.TauCeti.summatory N w a -
        ∫ t in _root_.Set.Ioc a b, _root_.deriv g t * _root_.TauCeti.summatory N w t := by
  have key := _root_.sum_mul_eq_sub_sub_integral_mul (_root_.TauCeti.normFiberSum N w) ha hab hg_diff hg_int
  have hL : ∑ n ∈ _root_.Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g (n : ℝ) * _root_.TauCeti.normFiberSum N w n =
      _root_.TauCeti.summatory N (fun i ↦ w i * g (N i)) b - _root_.TauCeti.summatory N (fun i ↦ w i * g (N i)) a := by
    simp_rw [← _root_.TauCeti.normFiberSum_mul N w g]
    exact _root_.TauCeti.sum_Ioc_normFiberSum N _ ha hab
  have hI : ∫ t in _root_.Set.Ioc a b, _root_.deriv g t * ∑ n ∈ _root_.Finset.Icc 0 ⌊t⌋₊, _root_.TauCeti.normFiberSum N w n =
      ∫ t in _root_.Set.Ioc a b, _root_.deriv g t * _root_.TauCeti.summatory N w t :=
    _root_.MeasureTheory.setIntegral_congr_fun _root_.measurableSet_Ioc fun t ht ↦ by
      rw [_root_.TauCeti.summatory_eq_sum_Icc_normFiberSum N w (ha.trans ht.1.le)]
  rw [hL, ← _root_.TauCeti.summatory_eq_sum_Icc_normFiberSum N w (ha.trans hab),
    ← _root_.TauCeti.summatory_eq_sum_Icc_normFiberSum N w ha, hI] at key
  exact key





/-! ### Imaginary-power twists -/











/-! ### One-sided bounds for twisted sums -/





/-! ### The ideal and prime carriers of a number field -/

variable (K : Type*) [Field K] [NumberField K]







variable {K}









end TauCeti

end
end
