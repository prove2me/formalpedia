-- Prove2me | solution 1 for TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:40:30.127271+00:00
-- url     : https://prove2.me/submissions/3f9f9c4c-0e5f-4e97-b31a-2f9e51dc29b4

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_ResidueDegree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
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
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_TauCeti_card_filter_rationalPrimeBelow_le_finrank

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The residue degree of a height-one prime over `ℚ`

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file names the two
objects that description involves and records their elementary theory.

## Main definitions

* `TauCeti.rationalPrimeBelow 𝔭` is the rational prime below a height-one prime `𝔭` of `𝓞 K`,
  namely the absolute norm of `𝔭 ∩ ℤ`.
* `TauCeti.higherDegreePrimes K` is the set of height-one primes of `𝓞 K` whose residue degree
  over `ℚ` exceeds `1`.
* `TauCeti.primesDividing K n hn` is the finite set of height-one primes of `𝓞 K` whose rational
  prime below divides a nonzero integer `n`.

## Main results

* `TauCeti.absNorm_eq_rationalPrimeBelow_pow`: the absolute norm of `𝔭` is the rational prime
  below it raised to the residue degree.
* `TauCeti.mem_higherDegreePrimes_iff_not_prime_absNorm`: a height-one prime has residue degree
  above one exactly when its absolute norm is not a prime number.
* `TauCeti.rationalPrimeBelow_pow_le_absNorm`: the norm of `𝔭` is at least the rational prime
  below it raised to any power at most the residue degree.
* `TauCeti.mem_higherDegreePrimes_of_one_lt_inertiaDeg`: residue degree above one over an
  intermediate number field forces residue degree above one over `ℚ`.
* `TauCeti.card_filter_rationalPrimeBelow_le_finrank`: at most `[K : ℚ]` height-one primes have
  a given rational prime below them.
* `IsDedekindDomain.HeightOneSpectrum.encard_setOf_under_eq_le_finrank`: at most `[E : K]`
  height-one primes of `E` contract to a given height-one prime of an intermediate number field
  `K`.
* `IsDedekindDomain.HeightOneSpectrum.absNorm_dvd_rationalPrimeBelow_pow_finrank`: the absolute
  norm of `𝔭` divides `p ^ [K : ℚ]`, so the residue degree is at most the degree of the field.
* `TauCeti.asIdeal_eq_span_singleton_of_absNorm_eq_pow_finrank`: a prime of full residue degree
  is inert, that is, generated by the rational prime below it.
* `IsDedekindDomain.HeightOneSpectrum.intCast_mem_asIdeal_iff`: an integer belongs to a
  height-one prime exactly when the rational prime below it divides that integer.
* `TauCeti.mem_primesDividing`: the defining condition for membership in `primesDividing`.

## Implementation notes

`rationalPrimeBelow` is named rather than spelled out as `Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal)`
because the estimates downstream fibre the primes over it: keeping it a single head symbol is what
makes the fibrewise rewriting elaborate, and it is the object `Chebotarev` will name when it
compares a prime of `K` with the rational prime under it.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]



omit [NumberField K] in
@[simp]
theorem mem_higherDegreePrimes {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ higherDegreePrimes K ↔ 1 < Ideal.inertiaDeg 𝔭.asIdeal ℤ :=
  Iff.rfl

/-! ### The rational prime below a height-one prime -/







omit [NumberField K] in
/-- The rational prime below a height-one prime really is a prime number. -/
theorem prime_rationalPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (rationalPrimeBelow 𝔭).Prime := by
  have : NeZero 𝔭.asIdeal := ⟨𝔭.ne_bot⟩
  exact Nat.absNorm_under_prime 𝔭.asIdeal

/-- The absolute norm of a height-one prime is the rational prime below it raised to the residue
degree. -/
theorem absNorm_eq_rationalPrimeBelow_pow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔭.asIdeal =
      rationalPrimeBelow 𝔭 ^ Ideal.inertiaDeg 𝔭.asIdeal ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (Ideal.under ℤ 𝔭.asIdeal) 𝔭.asIdeal).symm



/-- The absolute norm of a height-one prime is at least the rational prime below it raised to any
exponent bounded by the residue degree.  The matching bound from above is the divisibility
`IsDedekindDomain.HeightOneSpectrum.absNorm_dvd_rationalPrimeBelow_pow_finrank`.  Use
`TauCeti.absNorm_eq_rationalPrimeBelow_pow` for the exact value instead, and
`TauCeti.mem_higherDegreePrimes` to supply the hypothesis at the common instance `n = 2`. -/
theorem rationalPrimeBelow_pow_le_absNorm {𝔭 : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hn : n ≤ Ideal.inertiaDeg 𝔭.asIdeal ℤ) : rationalPrimeBelow 𝔭 ^ n ≤ Ideal.absNorm 𝔭.asIdeal :=
  -- the norm is `p ^ f`, and `p` is at least `2`, so the power is monotone in the exponent
  absNorm_eq_rationalPrimeBelow_pow 𝔭 ▸
    Nat.pow_le_pow_right (prime_rationalPrimeBelow 𝔭).one_lt.le hn



/-! ### Fibring the primes over the rational primes below them -/





/-! ### Inert primes -/







/-! ### The primes dividing an integer -/









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
# The primes of residue degree above one are negligible

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file bounds the
contribution of the primes with `f ≥ 2`, the set `TauCeti.higherDegreePrimes K`: they number
`O(√x)` up to norm `x`, hence also `o(x / log x)`, and their Dirichlet series `∑ N(𝔭) ^ (-s)`
converges for every `s > 1/2`, with a bound that is uniform on `s ≥ 1`.

Two elementary inputs carry the whole argument.

* A prime with `f ≥ 2` has `N(𝔭) = p ^ f ≥ p ^ 2`, so it is *not* determined by a rational prime
  of size `N(𝔭)` but by one of size at most `√(N(𝔭))`.
* At most `[K : ℚ]` height-one primes lie over one rational prime, by the fundamental identity
  `∑ e f = [K : ℚ]`; this is the already available
  `TauCeti.card_filter_rationalPrimeBelow_le_finrank`, itself resting on
  `TauCeti.NumberField.card_primesOverFinset_le_finrank`.

Together these compare any finite sum over the degree-above-one primes with `[K : ℚ]` times a sum
over the rational primes with the exponent doubled, which is
`TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum` below.  Counting gives the
`O(√x)` bound, and summing `m ^ (-2s)` gives convergence for every `s > 1/2` together with a
bound on the partial Dirichlet series that is *uniform* on `s ≥ 1`.

## Main results

* `TauCeti.primeCount_higherDegreePrimes_le`: the explicit count
  `π_K(x; f ≥ 2) ≤ [K : ℚ] · √x`, with `TauCeti.primeCount_higherDegreePrimes_isBigO` and
  `TauCeti.primeCount_higherDegreePrimes_isLittleO` its `O(√x)` and `o(x / log x)` forms.
* `TauCeti.summable_absNorm_rpow_higherDegreePrimes`: `∑ N(𝔭) ^ (-s)` over the degree-above-one
  primes converges for every `s > 1/2`, in particular at `s = 1`.
* `TauCeti.primeTheta_higherDegreePrimes_isLittleO`: those primes carry weight `o(x)` in `ϑ_K`.
* `TauCeti.primeIdealZetaSum_higherDegreePrimes_le`: that sum, in Mathlib's
  `NumberField.Set.primeIdealZetaSum` vocabulary, is at most `2 [K : ℚ]` for every `s ≥ 1`.
* `TauCeti.sum_absNorm_rpow_le_finrank_mul_tsum` and
  `TauCeti.tsum_absNorm_rpow_le_finrank_mul_tsum`: the same fibring over *all* height-one primes,
  in finite and infinite form, for every `s > 1`.
* `TauCeti.tsum_absNorm_rpow_neg_two_le`: at `s = 2` that becomes the explicit
  `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]`.

No density-zero statement is proved here.  What this file supplies is the numerator half of
one: `NumberField.Set.HasDirichletDensity (higherDegreePrimes K) 0` asks for
`primeIdealZetaSum (higherDegreePrimes K) s / primeIdealZetaSum univ s → 0` as `s → 1⁺`, and the
bound below controls only the numerator.  Together with the divergence of the denominator it gives
`TauCeti.hasDirichletDensity_higherDegreePrimes` in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible`.  By contrast
`primeCount K (higherDegreePrimes K) =o[atTop] primeCount K univ`
would need a lower bound on the full prime count, which the prime ideal theorem supplies and
which is not available here; the `o(x / log x)` statement below is against the explicit
function `x / log x`, not against `π_K`.

## Implementation notes

The set `TauCeti.higherDegreePrimes` and the map `TauCeti.rationalPrimeBelow` the estimates fibre
over, together with their elementary norm and inertia theory, are algebraic rather than analytic
and live in `TauCeti.NumberTheory.NumberField.ResidueDegree`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, and J. Milne, *Algebraic Number Theory*,
  Chapter VIII, for the same estimate in the Dirichlet-density setting.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### Fibring a sum over the rational primes below the primes -/

/-- Comparison of a finite sum over height-one primes with a sum over the rational primes below
them: the fibres have at most `[K : ℚ]` elements. -/
theorem TauCeti.sum_comp_rationalPrimeBelow_le {g : ℕ → ℝ} {F : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    {T : _root_.Finset ℕ} (hg : ∀ m ∈ T, 0 ≤ g m) (hFT : ∀ 𝔭 ∈ F, _root_.TauCeti.rationalPrimeBelow 𝔭 ∈ T) :
    ∑ 𝔭 ∈ F, g (_root_.TauCeti.rationalPrimeBelow 𝔭) ≤ _root_.Module.finrank ℚ K * ∑ m ∈ T, g m := by
  rw [← _root_.Finset.sum_fiberwise_of_maps_to' hFT g, _root_.Finset.mul_sum]
  refine _root_.Finset.sum_le_sum fun m hm ↦ ?_
  rw [_root_.Finset.sum_const, _root_.nsmul_eq_mul]
  exact _root_.mul_le_mul_of_nonneg_right
    (mod_cast _root_.TauCeti.card_filter_rationalPrimeBelow_le_finrank F m) (hg m hm)

/-- Comparison of a finite sum over height-one primes with the *whole* sum over `ℕ`: fibring
costs a factor `[K : ℚ]`, and completing the finite rational-prime sum to its `tsum` costs
nothing because the summand is nonnegative. This is the shape both norm-sum bounds below
take, once each has compared its own summand termwise with `g (rationalPrimeBelow 𝔭)`. -/
theorem TauCeti.sum_comp_rationalPrimeBelow_le_finrank_mul_tsum {g : ℕ → ℝ} (hg : ∀ m, 0 ≤ g m)
    (hsum : _root_.Summable g) (F : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∑ 𝔭 ∈ F, g (_root_.TauCeti.rationalPrimeBelow 𝔭) ≤ _root_.Module.finrank ℚ K * ∑' m : ℕ, g m :=
  (_root_.TauCeti.sum_comp_rationalPrimeBelow_le (fun m _ ↦ hg m)
        fun _ ↦ _root_.Finset.mem_image_of_mem _root_.TauCeti.rationalPrimeBelow).trans
    (_root_.mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun m _ ↦ hg m) (_root_.Nat.cast_nonneg _))

/-! ### Counting the primes of residue degree above one -/











/-! ### Convergence of the prime Dirichlet series over the degree-above-one primes -/


/-- The key comparison: a finite sum of `N(𝔭) ^ (-s)` over primes of residue degree above one is
bounded by `[K : ℚ]` times the full sum of `m ^ (-2s)` over the natural numbers. -/
theorem solution {s : ℝ} (hs : 1 / 2 < s)
    {F : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))} (hF : ∀ 𝔭 ∈ F, 𝔭 ∈ _root_.TauCeti.higherDegreePrimes K) :
    ∑ 𝔭 ∈ F, (_root_.Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      _root_.Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)) := by
  have hs0 : 0 < s := by linarith
  have hsummable : _root_.Summable fun m : ℕ ↦ (m : ℝ) ^ (-(2 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  -- Compare each term with the corresponding term for the rational prime below it.
  have hterm : ∀ 𝔭 ∈ F, (_root_.Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      ((_root_.TauCeti.rationalPrimeBelow 𝔭 : ℝ)) ^ (-(2 * s)) := by
    intro 𝔭 h𝔭
    set a : ℝ := (_root_.TauCeti.rationalPrimeBelow 𝔭 : ℝ) with ha
    have ha1 : (1 : ℝ) ≤ a := by rw [ha]; exact_mod_cast (_root_.TauCeti.prime_rationalPrimeBelow 𝔭).one_lt.le
    have hle : a ^ (2 : ℕ) ≤ (_root_.Ideal.absNorm 𝔭.asIdeal : ℝ) := by
      rw [ha]
      exact_mod_cast _root_.TauCeti.rationalPrimeBelow_pow_le_absNorm (mem_higherDegreePrimes.mp (hF 𝔭 h𝔭))
    have hpow : a ^ (-(2 * s)) = (a ^ (2 : ℕ)) ^ (-s) := by
      rw [← _root_.Real.rpow_natCast a 2, ← _root_.Real.rpow_mul (by linarith)]
      congr 1
      push_cast
      ring
    rw [hpow]
    exact _root_.Real.rpow_le_rpow_of_nonpos (_root_.pow_pos (by linarith) 2) hle (by linarith)
  exact (_root_.Finset.sum_le_sum hterm).trans (_root_.TauCeti.sum_comp_rationalPrimeBelow_le_finrank_mul_tsum
    (fun m ↦ _root_.Real.rpow_nonneg (_root_.Nat.cast_nonneg m) _) hsummable F)





/-! ### All height-one primes -/







end TauCeti

end
end
