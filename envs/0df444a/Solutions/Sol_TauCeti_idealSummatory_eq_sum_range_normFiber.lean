-- Prove2me | solution 1 for TauCeti.idealSummatory_eq_sum_range_normFiber
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:04.447023+00:00
-- url     : https://prove2.me/submissions/17c18a19-74e3-4e35-b23f-ae89a05fc20a

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/



variable (K : Type*) [Field K] [NumberField K]













variable {K}

/-- The absolute norm of a nonzero integral ideal is at least `1`, as a real number. -/
theorem TauCeti.one_le_absNorm_real_of_nonZeroDivisors (I : (_root_.Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ _root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) := by
  exact_mod_cast _root_.Ideal.absNorm_pos_of_nonZeroDivisors I





/-! ### The prime base and the exponent of a prime-power ideal -/



























































variable (K)

/-! ### Summatory functions over ideals and over primes -/









/-- An ideal summatory function is the sum of its weight over the inclusive cutoff carrier. -/
theorem TauCeti.idealSummatory_apply {M : Type*} [_root_.AddCommMonoid M] (w : (_root_.Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    _root_.TauCeti.idealSummatory K w x = ∑ I ∈ _root_.TauCeti.idealsLE K x, w I :=
  _root_.TauCeti.summatory_apply _ w x

















/-- Below the cutoff `1` there is nothing to sum over the nonzero ideals. -/
theorem TauCeti.idealSummatory_eq_zero_of_lt_one {M : Type*} [_root_.AddCommMonoid M]
    (w : (_root_.Ideal (𝓞 K))⁰ → M) {x : ℝ} (hx : x < 1) :
    _root_.TauCeti.idealSummatory K w x = 0 :=
  _root_.TauCeti.summatory_eq_zero_of_lt _ _root_.TauCeti.one_le_absNorm_real_of_nonZeroDivisors hx w





variable {K}

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)

open Classical in
/-- The ideals of absolute norm at most `x` and of absolute norm exactly `n` are the whole norm
fibre at `n`, as soon as `n` is at most `⌊x⌋₊`. -/
private theorem TauCeti.idealsLE_filter_absNorm_eq {n : ℕ} {x : ℝ} (hn : n ≤ ⌊x⌋₊) (hx : 0 ≤ x) :
    (_root_.TauCeti.idealsLE K x).filter (fun I : (_root_.Ideal (𝓞 K))⁰ ↦ _root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)) = n) =
      _root_.TauCeti.normFiber K n := by
  ext I
  simp only [_root_.Finset.mem_filter, _root_.TauCeti.mem_normLE, _root_.TauCeti.mem_normFiber]
  refine ⟨fun hI ↦ hI.2, fun hI ↦ ⟨?_, hI⟩⟩
  rw [hI]
  exact (Nat.cast_le.mpr hn).trans (_root_.Nat.floor_le hx)

/-- **Regrouping an ideal summatory function by absolute norm.** The inclusive sum of a weight over
the nonzero integral ideals of absolute norm at most `x` is the sum, over the natural numbers
`n ≤ ⌊x⌋₊`, of the total mass of the weight on the norm fibre at `n`.

This is the finite form of the Layer 1 regrouping: it reads a summatory function over ideals as a
partial sum of the `ArithmeticFunction` obtained from the same weight by `TauCeti.normCoeff`. -/
theorem solution {M : Type*} [_root_.AddCommMonoid M]
    (w : (_root_.Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    _root_.TauCeti.idealSummatory K w x = ∑ n ∈ _root_.Finset.range (⌊x⌋₊ + 1), ∑ I ∈ _root_.TauCeti.normFiber K n, w I := by
  classical
  rcases _root_.lt_or_ge x 1 with hx | hx
  · rw [_root_.TauCeti.idealSummatory_eq_zero_of_lt_one K w hx, Nat.floor_eq_zero.mpr hx]
    simp
  · rw [_root_.TauCeti.idealSummatory_apply,
      ← _root_.Finset.sum_fiberwise_of_maps_to
        (g := fun I : (_root_.Ideal (𝓞 K))⁰ ↦ _root_.Ideal.absNorm (I : _root_.Ideal (𝓞 K)))
        (t := _root_.Finset.range (⌊x⌋₊ + 1))
        (fun I hI ↦ Finset.mem_range_succ_iff.mpr (_root_.Nat.le_floor (by simpa using hI))) w]
    exact _root_.Finset.sum_congr _root_.rfl fun n hn ↦ by
      rw [_root_.TauCeti.idealsLE_filter_absNorm_eq K (Finset.mem_range_succ_iff.mp hn) (zero_le_one.trans hx)]





/-! ### The weighted prime counts -/





variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

























































end TauCeti

end
end
