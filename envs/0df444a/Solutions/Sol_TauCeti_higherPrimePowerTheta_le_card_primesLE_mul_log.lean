-- Prove2me | solution 1 for TauCeti.higherPrimePowerTheta_le_card_primesLE_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:38:18.101355+00:00
-- url     : https://prove2.me/submissions/d94a7ee4-f0aa-4dcc-99fa-27e9b068da81

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_HigherPrimePowers
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
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
import Theorems.Thm_TauCeti_card_mul_log_absNorm_le_of_pow_le_of_base_eq

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















/-- The absolute norm of a prime-power ideal is the corresponding power of the norm of its
prime base. -/
theorem absNorm_eq_absNorm_primePowerBase_pow (A : IdealPrimePower K) :
    Ideal.absNorm (A : Ideal (𝓞 K)) =
      Ideal.absNorm (primePowerBase A).asIdeal ^ primePowerExponent A := by
  rw [← primePowerBase_pow_primePowerExponent A, map_pow]

/-- **Membership in the prime-power cutoff, read off the base and the exponent.** The cutoff
bounds a prime power's own absolute norm, and that norm is `N(𝔭) ^ k`, so membership is exactly
the bound the counting arguments use. Both steps are equivalences, so this is an `iff`.

Deliberately not `@[simp]`: `mem_normLE` already carries `@[simp, grind =]` on the same
reducible head and would compete with it. -/
theorem mem_primePowersLE_iff {x : ℝ} {A : IdealPrimePower K} :
    A ∈ primePowersLE K x ↔
      ((Ideal.absNorm (primePowerBase A).asIdeal : ℝ)) ^ primePowerExponent A ≤ x := by
  rw [mem_normLE, absNorm_eq_absNorm_primePowerBase_pow, Nat.cast_pow]







/-- A prime-power ideal has exponent one exactly when it is itself prime. -/
@[simp] theorem primePowerExponent_eq_one_iff (A : IdealPrimePower K) :
    primePowerExponent A = 1 ↔ Prime (A : Ideal (𝓞 K)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ primePowerExponent_eq h (pow_one _)⟩
  rw [← primePowerBase_pow_primePowerExponent A, h, pow_one]
  exact prime_primePowerBase A

/-- A prime-power ideal which is not prime has exponent at least two. -/
theorem two_le_primePowerExponent {A : IdealPrimePower K} (hA : ¬ Prime (A : Ideal (𝓞 K))) :
    2 ≤ primePowerExponent A := by
  have h₁ := primePowerExponent_pos A
  have h₂ : primePowerExponent A ≠ 1 := fun h ↦ hA ((primePowerExponent_eq_one_iff A).mp h)
  omega































variable (K)

/-! ### Summatory functions over ideals and over primes -/













/-- A prime-power summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primePowerSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M) (x : ℝ) :
    primePowerSummatory K w x = ∑ A ∈ primePowersLE K x, w A :=
  summatory_apply _ w x



















variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

























































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
# Crude prime counts and the higher prime powers of a number field

Chebyshev's `ψ` counts every prime power `𝔭 ^ k` with the logarithmic weight `log N(𝔭)`, while
`ϑ` counts only the primes themselves.  Their difference is the sum of `log N(𝔭)` over the
*higher* prime powers, those with `k ≥ 2`, and the point of this file is that this difference is
negligible: it is `O(√x log² x)`, hence `o(x)`.

Two elementary counting bounds carry the argument.

* `TauCeti.two_pow_card_le_absNorm`: distinct primes dividing a nonzero ideal `I` each contribute
  a factor of at least `2` to `N(I)`, so there are at most `log₂ N(I)` of them.
* `TauCeti.card_primesLE_mul_log_two_le`: every prime of norm at most `x` divides the principal
  ideal generated by `⌊x⌋₊ !`, whose absolute norm is `(⌊x⌋₊ !) ^ [K:ℚ]`.  Feeding that into the
  previous bound gives `π_K(x) ≤ [K:ℚ] / log 2 · x log x`.

Neither bound is sharp — the true order of `π_K(x)` is `x / log x` — but they are proved from
scratch, with no analytic input and an explicit constant, and they are strong enough for every
estimate below.  The repository's existing effective count
`NumberField.card_ideal_absNorm_le`, which bounds the number of nonzero ideals of norm at most `X`
by `X² · 2 ^ [K:ℚ]`, is not: being quadratic it only gives `π_K(√x) = O(x)`, which loses the
saving that makes the higher prime powers negligible.

The higher prime powers are then summed by fibring over the prime base: for a fixed prime `𝔭`,
the exponents `k ≥ 2` with `N(𝔭) ^ k ≤ x` number at most `log x / log N(𝔭)`, so the whole fibre
contributes at most `log x`.  Since a higher prime power of norm at most `x` has
`N(𝔭) ^ 2 ≤ x`, only the primes of norm at most `√x` occur, and the total is at most
`π_K(√x) · log x`.

## Main definitions

* `TauCeti.higherPrimePowerWeight` is the standard logarithmic prime-power weight `log N(𝔭)`,
  restricted to the prime powers `𝔭 ^ k` with `k ≥ 2` and set to zero on the primes themselves.
* `TauCeti.higherPrimePowerTheta` is its inclusive summatory function, that is, `ψ - ϑ`.

## Main results

* `TauCeti.primeCount_le_mul_log` and `TauCeti.primeCount_isBigO`: the crude prime count.
* `TauCeti.higherPrimePowerTheta_le`: the explicit bound
  `ψ(x) - ϑ(x) ≤ [K:ℚ] / (2 log 2) · √x log² x`.
* `TauCeti.higherPrimePowerTheta_isBigO` and `TauCeti.higherPrimePowerTheta_isLittleO`: the
  `O(√x log² x)` and `o(x)` forms.
* `TauCeti.primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight`: the same conclusion for
  any normed additive-group-valued prime-power weight whose norm is dominated by a constant
  multiple of the standard one.  This isolates exactly the hypothesis another arithmetic weight
  has to supply.
* `TauCeti.primePowerSummatory_indicator_isLittleO`: its specialization to the higher prime powers
  whose base lies in a prescribed set of primes.

## Roadmap role

This is the prime and prime-power half of Layer **5.1** together with Layer **5.2** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, whose target 5.2 asks for "the generic
`O(√x log² x)` estimate under the standard logarithmic prime-power weight" and for the
hypotheses needed by other arithmetic weights.  Layer 10.2 consumes it as the named estimate
turning an asymptotic for `ψ` into one for `ϑ`; the roadmap's own accounting there requires only
the `o(x)` corollary.

The ideal-counting half of Layer 5.1 is a separate estimate: it is analytic, resting on Mathlib's
`NumberField.Ideal.tendsto_norm_le_div_atTop₀`, and is not needed here.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 7.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### Counting the primes below a cutoff -/











/-! ### The standard logarithmic weight on the higher prime powers -/



/-- On a higher prime power, the standard weight is the logarithm of the norm of the base. -/
@[simp] theorem TauCeti.higherPrimePowerWeight_of_two_le_primePowerExponent {A : _root_.TauCeti.IdealPrimePower K}
    (hA : 2 ≤ _root_.TauCeti.primePowerExponent A) :
    _root_.TauCeti.higherPrimePowerWeight A = _root_.Real.log (_root_.Ideal.absNorm (_root_.TauCeti.primePowerBase A).asIdeal) :=
  _root_.if_pos hA

/-- On a prime, the standard weight vanishes. -/
@[simp] theorem TauCeti.higherPrimePowerWeight_of_prime {A : _root_.TauCeti.IdealPrimePower K}
    (hA : _root_.Prime (A : _root_.Ideal (𝓞 K))) : _root_.TauCeti.higherPrimePowerWeight A = 0 := by
  have hexp : _root_.TauCeti.primePowerExponent A = 1 := (_root_.TauCeti.primePowerExponent_eq_one_iff A).mpr hA
  exact _root_.if_neg (by omega)









/-- The higher-prime-power theta function is the summatory function of the standard weight. -/
@[simp]
theorem TauCeti.higherPrimePowerTheta_apply (K : Type*) [_root_.Field K] [_root_.NumberField K] (x : ℝ) :
    _root_.TauCeti.higherPrimePowerTheta K x = _root_.TauCeti.primePowerSummatory K _root_.TauCeti.higherPrimePowerWeight x := by
  rw [_root_.TauCeti.higherPrimePowerTheta]





/-! ### The `O(√x log² x)` estimate -/

/-- Fibring the higher prime powers over their prime base: for a fixed prime `𝔭`, the exponents
`k ≥ 2` with `N(𝔭) ^ k ≤ x` contribute at most `log x` in total, and only primes of norm at most
`√x` occur at all. -/
theorem solution
    (K : Type*) [_root_.Field K] [_root_.NumberField K] {x : ℝ} (hx : 1 ≤ x) :
    _root_.TauCeti.higherPrimePowerTheta K x ≤ (_root_.TauCeti.primesLE K (_root_.Real.sqrt x)).card * _root_.Real.log x := by
  classical
  have hx0 : (0 : ℝ) < x := _root_.lt_of_lt_of_le _root_.zero_lt_one hx
  have hlogx : 0 ≤ _root_.Real.log x := _root_.Real.log_nonneg hx
  set T := (_root_.TauCeti.primePowersLE K x).filter (fun A ↦ 2 ≤ _root_.TauCeti.primePowerExponent A) with hTdef
  have hmemT : ∀ A ∈ T, ((_root_.Ideal.absNorm (_root_.TauCeti.primePowerBase A).asIdeal : ℝ)) ^ _root_.TauCeti.primePowerExponent A
      ≤ x ∧ 2 ≤ _root_.TauCeti.primePowerExponent A := by
    intro A hA
    rw [hTdef, _root_.Finset.mem_filter] at hA
    exact ⟨mem_primePowersLE_iff.mp hA.1, hA.2⟩
  have hsub : T ⊆ _root_.TauCeti.primePowersLE K x := _root_.Finset.filter_subset _ _
  have hzero : ∀ A ∈ _root_.TauCeti.primePowersLE K x, A ∉ T → _root_.TauCeti.higherPrimePowerWeight A = 0 := by
    intro A hA hAT
    refine _root_.TauCeti.higherPrimePowerWeight_of_prime ?_
    by_contra hprime
    exact hAT (Finset.mem_filter.mpr ⟨hA, _root_.TauCeti.two_le_primePowerExponent hprime⟩)
  have hsum : _root_.TauCeti.higherPrimePowerTheta K x
      = ∑ A ∈ T, _root_.Real.log (_root_.Ideal.absNorm (_root_.TauCeti.primePowerBase A).asIdeal) := by
    rw [_root_.TauCeti.higherPrimePowerTheta_apply, _root_.TauCeti.primePowerSummatory_apply, ← _root_.Finset.sum_subset hsub hzero]
    exact _root_.Finset.sum_congr _root_.rfl fun A hA ↦
      _root_.TauCeti.higherPrimePowerWeight_of_two_le_primePowerExponent (hmemT A hA).2
  have hmaps : ∀ A ∈ T, _root_.TauCeti.primePowerBase A ∈ _root_.TauCeti.primesLE K (_root_.Real.sqrt x) := by
    intro A hA
    obtain ⟨hle, hexp⟩ := hmemT A hA
    have hq : (2 : ℝ) ≤ _root_.Ideal.absNorm (_root_.TauCeti.primePowerBase A).asIdeal :=
      _root_.TauCeti.two_le_absNorm_asIdeal_real _
    rw [_root_.TauCeti.mem_normLE, _root_.Real.le_sqrt (by linarith) hx0.le]
    exact _root_.le_trans (_root_.pow_le_pow_right₀ (by linarith) hexp) hle
  rw [hsum, ← _root_.Finset.sum_fiberwise_of_maps_to' hmaps
    (fun v ↦ _root_.Real.log (_root_.Ideal.absNorm v.asIdeal))]
  refine (_root_.Finset.sum_le_card_nsmul _ _ (_root_.Real.log x) ?_).trans_eq (by rw [_root_.nsmul_eq_mul])
  intro v _
  rw [_root_.Finset.sum_const, _root_.nsmul_eq_mul]
  exact _root_.TauCeti.card_mul_log_absNorm_le_of_pow_le_of_base_eq hx
    (fun A hA ↦ by
      obtain ⟨hle, -⟩ := hmemT A (_root_.Finset.mem_of_mem_filter _ hA)
      rwa [(Finset.mem_filter.mp hA).2] at hle)
    (fun A hA ↦ (Finset.mem_filter.mp hA).2)









/-! ### Other arithmetic weights -/







end TauCeti

end
end
