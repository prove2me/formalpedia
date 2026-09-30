-- Prove2me | solution 1 for TauCeti.primeCount_eq_primeTheta_div_log_add_integral
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:40:05.757112+00:00
-- url     : https://prove2.me/submissions/a71f7e32-dd86-4268-8994-7fe39a3e479b

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
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
import Theorems.Thm_TauCeti_summatory_mul_eq_sub_sub_integral_mul

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















/-- Below a uniform lower bound for the `N`-values the carrier is empty. -/
theorem normLE_eq_empty_of_lt {b x : ℝ} (hb : ∀ i, b ≤ (N i : ℝ)) (hx : x < b) :
    normLE N x = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun i hi ↦ ?_
  exact absurd ((hb i).trans (mem_normLE N |>.mp hi)) (not_le.mpr hx)

/-! ### Generic summatory functions -/



/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]









/-- Below a uniform lower bound for the `N`-values every summatory function vanishes. -/
theorem summatory_eq_zero_of_lt {M : Type*} [AddCommMonoid M] {b x : ℝ}
    (hb : ∀ i, b ≤ (N i : ℝ)) (hx : x < b) (w : ι → M) : summatory N w x = 0 := by
  simp [summatory, normLE_eq_empty_of_lt N hb hx]



















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
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

`TauCeti.idealsLE_filter_dvd` identifies the ideals below a cutoff divisible by a fixed nonzero
ideal `P` with the multiples of `P`, and `TauCeti.idealSummatory_ite_dvd` reads the corresponding
part of a summatory function at the rescaled cutoff `x / N(P)`.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`; `TauCeti.idealSummatory_eq_sum_Icc_normCoeff` writes the same regrouping as a
partial sum of `TauCeti.normCoeff`.  Together they present a sum over prime powers as a partial
sum of an `ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density. In the same spirit,
`TauCeti.primeTheta_isLittleO_of_finite` records that a finite set of primes contributes an
eventually constant amount to `ϑ_K`, hence `o(x)`: an exceptional set can be discarded from a
counting argument outright, not merely from a density. Its `ψ` companion is
`TauCeti.primePsi_isLittleO_of_finite`.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/



variable (K : Type*) [Field K] [NumberField K]













variable {K}







/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/

/-- At a uniform lower-bound cutoff, twisting a weight by a function of its `N`-value multiplies
the summatory function by the value of the twist at that cutoff. -/
theorem summatory_mul_eq_mul_summatory_of_le {ι 𝕜 : Type*} (N : ι → ℕ) [Northcott N]
    [NonUnitalCommSemiring 𝕜] {a : ℝ} (ha : ∀ i, a ≤ N i) (w : ι → 𝕜) (g : ℝ → 𝕜) :
    summatory N (fun i ↦ w i * g (N i)) a = g a * summatory N w a := by
  rw [summatory_apply, summatory_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [le_antisymm ((mem_normLE N).mp hi) (ha i), mul_comm]









/-- A prime summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primeSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) :
    primeSummatory K w x = ∑ v ∈ primesLE K x, w v :=
  summatory_apply _ w x





















variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

/-- The logarithmically weighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeTheta_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x =
      ∑ v ∈ primesLE K x, S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v :=
  by rw [primeTheta, primeSummatory_apply]

/-- The unweighted prime count as an explicit sum over the inclusive carrier. -/
theorem primeCount_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∑ v ∈ primesLE K x, S.indicator 1 v := by
  rw [primeCount, primeSummatory_apply]











/-- The logarithm of the absolute norm of a height-one prime is positive. -/
theorem log_absNorm_asIdeal_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  Real.log_pos (by linarith [two_le_absNorm_asIdeal_real v])









































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











/-! ### Abel summation over a Northcott carrier -/



/-- Abel summation from a real cutoff `a` for a carrier all of whose indices have `N`-value at
least `a`. The boundary term at `a` cancels, because there the twisted weight is `g a` times the
untwisted one.

The identity holds for every cutoff `b`: below `a` all three terms vanish. -/
theorem TauCeti.summatory_mul_eq_sub_integral_mul_of_le {a : ℝ} (ha : 0 ≤ a)
    (hN : ∀ i, a ≤ (N i : ℝ)) (w : ι → 𝕜) {g : ℝ → 𝕜} (b : ℝ)
    (hg_diff : ∀ t ∈ _root_.Set.Icc a b, _root_.DifferentiableAt ℝ g t)
    (hg_int : _root_.MeasureTheory.IntegrableOn (_root_.deriv g) (_root_.Set.Icc a b)) :
    _root_.TauCeti.summatory N (fun i ↦ w i * g (N i)) b =
      g b * _root_.TauCeti.summatory N w b - ∫ t in _root_.Set.Ioc a b, _root_.deriv g t * _root_.TauCeti.summatory N w t := by
  rcases _root_.lt_or_ge b a with hb | hb
  · rw [_root_.TauCeti.summatory_eq_zero_of_lt N hN hb, _root_.TauCeti.summatory_eq_zero_of_lt N hN hb,
      _root_.Set.Ioc_eq_empty_of_le hb.le]
    simp
  · have key := _root_.TauCeti.summatory_mul_eq_sub_sub_integral_mul N w ha hb hg_diff hg_int
    rw [_root_.TauCeti.summatory_mul_eq_mul_summatory_of_le N hN w g] at key
    linear_combination key



/-! ### Imaginary-power twists -/











/-! ### One-sided bounds for twisted sums -/





/-! ### The ideal and prime carriers of a number field -/

variable (K : Type*) [Field K] [NumberField K]





/-- Abel summation over the height-one primes of `𝓞 K`, from the cutoff `2`. -/
theorem TauCeti.primeSummatory_mul_eq_sub_integral_mul (w : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) {g : ℝ → ℝ}
    (x : ℝ) (hg_diff : ∀ t ∈ _root_.Set.Icc 2 x, _root_.DifferentiableAt ℝ g t)
    (hg_int : _root_.MeasureTheory.IntegrableOn (_root_.deriv g) (_root_.Set.Icc 2 x)) :
    _root_.TauCeti.primeSummatory K (fun v ↦ w v * g (_root_.Ideal.absNorm v.asIdeal)) x =
      g x * _root_.TauCeti.primeSummatory K w x - ∫ t in _root_.Set.Ioc 2 x, _root_.deriv g t * _root_.TauCeti.primeSummatory K w t :=
  _root_.TauCeti.summatory_mul_eq_sub_integral_mul_of_le _ (by norm_num) _root_.TauCeti.two_le_absNorm_asIdeal_real w x
    hg_diff hg_int

variable {K}

private theorem TauCeti.primeTheta_eq_primeSummatory (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    _root_.TauCeti.primeTheta K S x =
      _root_.TauCeti.primeSummatory K (S.indicator fun v ↦ _root_.Real.log (_root_.Ideal.absNorm v.asIdeal : ℝ)) x := by
  rw [_root_.TauCeti.primeTheta_apply, _root_.TauCeti.primeSummatory_apply]

private theorem TauCeti.primeCount_eq_primeSummatory (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    _root_.TauCeti.primeCount K S x = _root_.TauCeti.primeSummatory K (S.indicator 1) x := by
  rw [_root_.TauCeti.primeCount_apply, _root_.TauCeti.primeSummatory_apply]



/-- **Chebyshev's `π` from `ϑ`.**  The unweighted prime count is recovered from the logarithmically
weighted one by Abel summation.  This is the finite identity whose two terms Layer 6.2 estimates
in order to turn `ϑ(x) ∼ δx` into `π(x) ∼ δ Li(x)`. -/
theorem solution (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (x : ℝ) :
    _root_.TauCeti.primeCount K S x = _root_.TauCeti.primeTheta K S x / _root_.Real.log x +
      ∫ t in _root_.Set.Ioc 2 x, _root_.TauCeti.primeTheta K S t / (t * _root_.Real.log t ^ 2) := by
  have hw : (fun v : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
      S.indicator (fun v ↦ _root_.Real.log (_root_.Ideal.absNorm v.asIdeal : ℝ)) v *
        (_root_.Real.log (_root_.Ideal.absNorm v.asIdeal : ℝ))⁻¹) =
      S.indicator (1 : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) := by
    funext v
    by_cases hv : v ∈ S
    · rw [_root_.Set.indicator_of_mem hv, _root_.Set.indicator_of_mem hv, _root_.Pi.one_apply,
        _root_.mul_inv_cancel₀ (_root_.TauCeti.log_absNorm_asIdeal_pos v).ne']
    · rw [_root_.Set.indicator_of_notMem hv, _root_.Set.indicator_of_notMem hv, _root_.MulZeroClass.zero_mul]
  have hdiff : ∀ t ∈ _root_.Set.Icc (2 : ℝ) x, _root_.DifferentiableAt ℝ (fun u : ℝ ↦ (_root_.Real.log u)⁻¹) t :=
    fun t ht ↦ _root_.Real.differentiableAt_inv_log (by linarith [ht.1] : (0 : ℝ) < t).ne'
      (by linarith [ht.1] : (1 : ℝ) < t).ne' (by linarith [ht.1] : (-1 : ℝ) < t).ne'
  have hint : _root_.MeasureTheory.IntegrableOn (_root_.deriv fun u : ℝ ↦ (_root_.Real.log u)⁻¹) (_root_.Set.Icc (2 : ℝ) x) := by
    rw [_root_.Real.deriv_inv_log]
    refine _root_.ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    exact (((continuousAt_id.inv₀ ht0).neg).div ((_root_.Real.continuousAt_log ht0).pow 2)
      (_root_.pow_ne_zero 2 (_root_.Real.log_pos (by linarith [ht.1])).ne')).continuousWithinAt
  have key : _root_.TauCeti.primeCount K S x = (_root_.Real.log x)⁻¹ * _root_.TauCeti.primeTheta K S x -
      ∫ t in _root_.Set.Ioc (2 : ℝ) x, _root_.deriv (fun u : ℝ ↦ (_root_.Real.log u)⁻¹) t * _root_.TauCeti.primeTheta K S t := by
    simp only [_root_.TauCeti.primeCount_eq_primeSummatory, _root_.TauCeti.primeTheta_eq_primeSummatory]
    rw [← hw]
    exact _root_.TauCeti.primeSummatory_mul_eq_sub_integral_mul K _ x hdiff hint
  have hI : ∫ t in _root_.Set.Ioc (2 : ℝ) x, _root_.deriv (fun u : ℝ ↦ (_root_.Real.log u)⁻¹) t * _root_.TauCeti.primeTheta K S t =
      -∫ t in _root_.Set.Ioc (2 : ℝ) x, _root_.TauCeti.primeTheta K S t / (t * _root_.Real.log t ^ 2) := by
    rw [← _root_.MeasureTheory.integral_neg]
    refine _root_.MeasureTheory.setIntegral_congr_fun _root_.measurableSet_Ioc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlog : _root_.Real.log t ≠ 0 := (_root_.Real.log_pos (by linarith [ht.1])).ne'
    rw [_root_.Real.deriv_inv_log_apply]
    field_simp
  rw [key, hI]
  ring

end TauCeti

end
end
