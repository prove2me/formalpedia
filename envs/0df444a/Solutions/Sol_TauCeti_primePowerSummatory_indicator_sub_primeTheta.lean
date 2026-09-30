-- Prove2me | solution 1 for TauCeti.primePowerSummatory_indicator_sub_primeTheta
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:26:29.156952+00:00
-- url     : https://prove2.me/submissions/fe017021-6818-4c60-8f1a-dea220cfc424

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_HigherPrimePowers
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus
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



/-- Summation distributes over pointwise addition of weights. -/
theorem summatory_add {M : Type*} [AddCommMonoid M] (w₁ w₂ : ι → M) (x : ℝ) :
    summatory N (w₁ + w₂) x = summatory N w₁ x + summatory N w₂ x := by
  simp [summatory, Finset.sum_add_distrib]

























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



/-- The ideal underlying `TauCeti.IdealPrimePower.ofPrime v` is the prime ideal of `v`. -/
@[simp]
theorem IdealPrimePower.coe_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    (IdealPrimePower.ofPrime v : Ideal (𝓞 K)) = v.asIdeal :=
  (rfl)

/-- The underlying ideal of a height-one prime is prime. -/
theorem IdealPrimePower.prime_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    Prime ((IdealPrimePower.ofPrime v : IdealPrimePower K) : Ideal (𝓞 K)) :=
  Ideal.prime_of_isPrime v.ne_bot v.isPrime

/-- A height-one prime is its own prime base. -/
@[simp]
theorem primePowerBase_ofPrime (v : HeightOneSpectrum (𝓞 K)) :
    primePowerBase (IdealPrimePower.ofPrime v) = v :=
  HeightOneSpectrum.ext
    (primePowerBase_asIdeal_eq (IdealPrimePower.prime_ofPrime v) (pow_one _))



/-- A prime prime-power ideal is its own prime base, seen as a prime-power ideal. -/
@[simp]
theorem IdealPrimePower.ofPrime_primePowerBase {A : IdealPrimePower K}
    (hA : Prime (A : Ideal (𝓞 K))) : IdealPrimePower.ofPrime (primePowerBase A) = A := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [IdealPrimePower.coe_ofPrime, ← primePowerBase_pow_primePowerExponent A,
    (primePowerExponent_eq_one_iff A).mpr hA, pow_one]

/-- Below a cutoff, the prime-power ideals which are themselves prime are exactly the images
under `TauCeti.IdealPrimePower.ofPrime` of the height-one primes below that cutoff. -/
private theorem primePowersLE_filter_prime (x : ℝ)
    [DecidablePred fun A : IdealPrimePower K ↦ Prime (A : Ideal (𝓞 K))] :
    (primePowersLE K x).filter (fun A : IdealPrimePower K ↦ Prime (A : Ideal (𝓞 K)))
      = (primesLE K x).image IdealPrimePower.ofPrime := by
  ext A
  simp only [Finset.mem_filter, Finset.mem_image, mem_normLE]
  refine ⟨fun ⟨hle, hA⟩ ↦ ⟨primePowerBase A, ?_, IdealPrimePower.ofPrime_primePowerBase hA⟩,
    fun ⟨v, hv, hvA⟩ ↦ ?_⟩
  · have hbase : ((IdealPrimePower.ofPrime (primePowerBase A) : IdealPrimePower K) :
        Ideal (𝓞 K)) = (A : Ideal (𝓞 K)) :=
      congrArg (fun B : IdealPrimePower K ↦ (B : Ideal (𝓞 K)))
        (IdealPrimePower.ofPrime_primePowerBase hA)
    rw [IdealPrimePower.coe_ofPrime] at hbase
    rw [hbase]
    exact hle
  · subst hvA
    exact ⟨hv, IdealPrimePower.prime_ofPrime v⟩

















variable (K)

/-! ### Summatory functions over ideals and over primes -/











/-- A prime summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primeSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) :
    primeSummatory K w x = ∑ v ∈ primesLE K x, w v :=
  summatory_apply _ w x

/-- A prime-power summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem primePowerSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M) (x : ℝ) :
    primePowerSummatory K w x = ∑ A ∈ primePowersLE K x, w A :=
  summatory_apply _ w x

/-- A prime-power weight vanishing off the primes themselves has the same summatory function as
its restriction to the primes.  This is what separates the exponent-one part of a sum over prime
powers, such as Chebyshev's `ϑ` inside `ψ`. -/
theorem primePowerSummatory_eq_primeSummatory {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M)
    (hw : ∀ A : IdealPrimePower K, ¬ Prime (A : Ideal (𝓞 K)) → w A = 0) (x : ℝ) :
    primePowerSummatory K w x =
      primeSummatory K (fun v ↦ w (IdealPrimePower.ofPrime v)) x := by
  classical
  rw [primePowerSummatory_apply, primeSummatory_apply,
    ← Finset.sum_filter_of_ne (p := fun A : IdealPrimePower K ↦ Prime (A : Ideal (𝓞 K)))
      fun A _ hne ↦ not_not.mp fun h ↦ hne (hw A h),
    primePowersLE_filter_prime]
  exact Finset.sum_image fun v _ w' _ h ↦ HeightOneSpectrum.ext
    (by simpa using congrArg (fun B : IdealPrimePower K ↦ (B : Ideal (𝓞 K))) h)

/-- Prime-power summation distributes over pointwise addition of weights. -/
theorem primePowerSummatory_add {M : Type*} [AddCommMonoid M]
    (w₁ w₂ : IdealPrimePower K → M) (x : ℝ) :
    primePowerSummatory K (w₁ + w₂) x =
      primePowerSummatory K w₁ x + primePowerSummatory K w₂ x :=
  summatory_add _ _ _ x















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

open _root_.Filter _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### Counting the primes below a cutoff -/











/-! ### The standard logarithmic weight on the higher prime powers -/



/-- On a higher prime power, the standard weight is the logarithm of the norm of the base. -/
@[simp] theorem higherPrimePowerWeight_of_two_le_primePowerExponent {A : IdealPrimePower K}
    (hA : 2 ≤ primePowerExponent A) :
    higherPrimePowerWeight A = Real.log (Ideal.absNorm (primePowerBase A).asIdeal) :=
  if_pos hA

/-- On a prime, the standard weight vanishes. -/
@[simp] theorem higherPrimePowerWeight_of_prime {A : IdealPrimePower K}
    (hA : Prime (A : Ideal (𝓞 K))) : higherPrimePowerWeight A = 0 := by
  have hexp : primePowerExponent A = 1 := (primePowerExponent_eq_one_iff A).mpr hA
  exact if_neg (by omega)















/-! ### The `O(√x log² x)` estimate -/











/-! ### Other arithmetic weights -/







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
# Chebyshev's `ψ` for a set of prime ideals, and the removal of the higher prime powers

For a set `S` of height-one primes of the ring of integers of a number field `K`, Chebyshev's
`ψ` weights *every* prime power `𝔭 ^ k` with `𝔭 ∈ S` and `k ≥ 1` by `log N(𝔭)`, while `ϑ` weights
only the primes themselves.  This file defines `ψ`, proves that the difference `ψ - ϑ` is exactly
the higher-prime-power sum estimated in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/HigherPrimePowers.lean`, and spends that estimate
on the transfer of an asymptotic `ψ(x) = δ x + o(x)` to `ϑ(x) = δ x + o(x)`.

Prime powers with `k ≥ 2` are kept visible throughout: `ψ` is *defined* with all of them present,
and their removal is a named hypothesis, `TauCeti.HasNegligibleHigherPrimePowers`, discharged for
the standard logarithmic weight by `TauCeti.standardPrimePowerRemoval`.  A different coefficient
system does not get that hypothesis for free; what it has to supply is the domination bound of
`TauCeti.primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight`.

## Main definitions

* `TauCeti.primePowerWeight` is the standard logarithmic prime-power weight, the value `log N(𝔭)`
  at `𝔭 ^ k` for every `k ≥ 1`.  It is the real form of the ideal von Mangoldt function of Layer 2
  on the prime powers.
* `TauCeti.primePsi` is its inclusive summatory function over the prime powers whose base lies in
  `S`: the number-field analogue of Chebyshev's `ψ`.
* `TauCeti.HasNegligibleHigherPrimePowers K S` says that `ψ - ϑ` is `o(x)`.
* `TauCeti.primeVonMangoldtWeight` is the same weight spread over *all* nonzero ideals, zero away
  from the prime powers with base in `S`, and `TauCeti.primeVonMangoldtCoeff` is its regrouping by
  absolute norm, an `ArithmeticFunction ℝ`.

## Main results

* `TauCeti.primePowerSummatory_indicator_sub_primeTheta` splits the exponent-one part off the
  standard weight restricted to any set of prime powers containing exactly the primes of `S`.
* `TauCeti.primePsi_sub_primeTheta` identifies `ψ - ϑ` with the higher-prime-power sum.
* `TauCeti.primePsi_le_ncard_mul_log`: for `x ≥ 1`, a finite set of primes contributes at most
  `#S · log x` to `ψ`, with `TauCeti.primePsi_isBigO_log_of_finite` and
  `TauCeti.primePsi_isLittleO_of_finite` its asymptotic forms.
* `TauCeti.standardPrimePowerRemoval` proves `HasNegligibleHigherPrimePowers K S` for every `S`,
  from the Layer 5 estimate `ψ(x) - ϑ(x) = O(√x log² x)`.
* `TauCeti.primeTheta_asymptotic_of_primePsi` and
  `TauCeti.primePsi_asymptotic_of_primeTheta` transfer a linear asymptotic across that difference,
  with `TauCeti.primeTheta_isEquivalent_of_primePsi` the equivalence form for a nonzero density.
* `TauCeti.primePsi_eq_sum_range` presents `ψ(x)` as the inclusive partial sum
  `∑_{n ≤ ⌊x⌋₊} a n` of the coefficient system, whose coefficients are nonnegative
  (`TauCeti.primeVonMangoldtCoeff_nonneg`) and supported on the prime powers
  (`TauCeti.primeVonMangoldtCoeff_eq_zero_of_not_isPrimePow`).
* `TauCeti.normCoeff_vonMangoldt` identifies the coefficient system of the full prime carrier with
  the Layer 1 regrouping of the Layer 2 ideal von Mangoldt function.
* `TauCeti.primeVonMangoldtCoeff_rat_natGenerator_pow` evaluates the coefficient system of any set
  of primes of `𝓞 ℚ` at a prime power, and `TauCeti.primeVonMangoldtCoeff_rat_le` bounds it by
  Mathlib's von Mangoldt function `Λ`.

## Roadmap role

This is Layer **10.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: "For the fixed
standard nonnegative logarithmic prime-power weight, use Layer 5 to prove
`standardPrimePowerRemoval : HasNegligibleHigherPrimePowers K S` and make
`primeTheta_asymptotic_of_primePsi` consume that named estimate."  It also supplies the arithmetic
half of Layer **10.1**, "Define `primePsi` with all prime powers present": the exact nonnegative
von Mangoldt coefficient system and the identity presenting `ψ` as its partial sum, which is the
shape in which a Tauberian theorem delivers its conclusion.  The analytic boundary package and
the resulting prime-number-theorem transfer are in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Boundary.lean`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 7.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.

The rational-prime case of `ψ`, `ϑ` and their difference is Mathlib's
`Mathlib/NumberTheory/Chebyshev.lean`, whose `Chebyshev.theta_le_psi` and
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` are the analogues of
`TauCeti.primeTheta_le_primePsi` and `TauCeti.standardPrimePowerRemoval`; nothing is transported
from there, since the estimate consumed here is proved over prime ideals in Layer 5.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter _root_.NumberField
open scoped _root_.Asymptotics _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### The standard logarithmic prime-power weight -/











/-- On a prime the standard weight is the logarithm of its own absolute norm. -/
@[simp]
theorem TauCeti.primePowerWeight_ofPrime (v : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    _root_.TauCeti.primePowerWeight (_root_.TauCeti.IdealPrimePower.ofPrime v) = _root_.Real.log (_root_.Ideal.absNorm v.asIdeal) := by
  rw [_root_.TauCeti.primePowerWeight, _root_.TauCeti.primePowerBase_ofPrime]

/-- Away from the primes the two prime-power weights agree: `TauCeti.higherPrimePowerWeight` is
the standard weight with its exponent-one part deleted. -/
theorem TauCeti.higherPrimePowerWeight_of_not_prime {A : _root_.TauCeti.IdealPrimePower K}
    (hA : ¬ _root_.Prime (A : _root_.Ideal (𝓞 K))) :
    _root_.TauCeti.higherPrimePowerWeight A = _root_.TauCeti.primePowerWeight A :=
  _root_.TauCeti.higherPrimePowerWeight_of_two_le_primePowerExponent (_root_.TauCeti.two_le_primePowerExponent hA)

/-! ### Chebyshev's `ψ` -/



variable {S : Set (HeightOneSpectrum (𝓞 K))} {x δ : ℝ}











/-! ### The higher prime powers as the gap between `ψ` and `ϑ` -/

/-- **Splitting the exponent-one part off a restricted prime-power sum.**  For a set `T` of prime
powers containing exactly the primes of `S`, the summatory function of the standard logarithmic
weight restricted to `T` exceeds `ϑ` by the higher-prime-power sum over `T`. -/
theorem solution (T : _root_.Set (_root_.TauCeti.IdealPrimePower K))
    (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hTS : ∀ v : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K), _root_.TauCeti.IdealPrimePower.ofPrime v ∈ T ↔ v ∈ S) (x : ℝ) :
    _root_.TauCeti.primePowerSummatory K (T.indicator _root_.TauCeti.primePowerWeight) x - _root_.TauCeti.primeTheta K S x =
      _root_.TauCeti.primePowerSummatory K (T.indicator _root_.TauCeti.higherPrimePowerWeight) x := by
  have hsplit : T.indicator _root_.TauCeti.primePowerWeight
      = T.indicator (_root_.TauCeti.primePowerWeight - _root_.TauCeti.higherPrimePowerWeight)
        + T.indicator _root_.TauCeti.higherPrimePowerWeight := by
    rw [← _root_.Set.indicator_add', _root_.sub_add_cancel]
  have hzero : ∀ A : _root_.TauCeti.IdealPrimePower K, ¬ _root_.Prime (A : _root_.Ideal (𝓞 K)) →
      T.indicator (_root_.TauCeti.primePowerWeight - _root_.TauCeti.higherPrimePowerWeight) A = 0 := fun A hA ↦ by
    simp [_root_.TauCeti.higherPrimePowerWeight_of_not_prime hA]
  have hexp : _root_.TauCeti.primePowerSummatory K
      (T.indicator (_root_.TauCeti.primePowerWeight - _root_.TauCeti.higherPrimePowerWeight)) x = _root_.TauCeti.primeTheta K S x := by
    rw [_root_.TauCeti.primePowerSummatory_eq_primeSummatory K _ hzero, _root_.TauCeti.primeSummatory_apply, _root_.TauCeti.primeTheta_apply]
    refine _root_.Finset.sum_congr _root_.rfl fun v _ ↦ ?_
    by_cases hv : v ∈ S
    · rw [_root_.Set.indicator_of_mem ((hTS v).mpr hv), _root_.Set.indicator_of_mem hv, _root_.Pi.sub_apply,
        _root_.TauCeti.higherPrimePowerWeight_of_prime (_root_.TauCeti.IdealPrimePower.prime_ofPrime v), _root_.sub_zero,
        _root_.TauCeti.primePowerWeight_ofPrime]
    · rw [_root_.Set.indicator_of_notMem (fun h ↦ hv ((hTS v).mp h)), _root_.Set.indicator_of_notMem hv]
  rw [hsplit, _root_.TauCeti.primePowerSummatory_add, hexp, _root_.add_sub_cancel_left]





/-! ### Removing the higher prime powers -/



















/-! ### The von Mangoldt coefficient system of a set of primes -/

















































end TauCeti

end
end
