-- Prove2me | solution 1 for TauCeti.card_primesLE_mul_log_two_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:26:31.037744+00:00
-- url     : https://prove2.me/submissions/decaaeeb-1ecf-4605-b95a-4bf0f18d2818

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



































end IdealArithmeticFunction

namespace MultiplicativeIdealWeight





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

/-- Distinct primes dividing a nonzero ideal `I` each contribute a factor of at least `2` to
`N(I)`, so `I` has at most `log₂ N(I)` distinct prime divisors. -/
theorem TauCeti.two_pow_card_le_absNorm {I : _root_.Ideal (𝓞 K)} (hI : I ≠ 0)
    {s : _root_.Finset (_root_.Ideal (𝓞 K))} (hprime : ∀ P ∈ s, _root_.Prime P) (hdvd : ∀ P ∈ s, P ∣ I) :
    2 ^ s.card ≤ _root_.Ideal.absNorm I := by
  have hprod : (∏ P ∈ s, P) ∣ I := _root_.Finset.prod_primes_dvd I hprime hdvd
  calc 2 ^ s.card = ∏ _P ∈ s, 2 := by rw [_root_.Finset.prod_const]
    _ ≤ ∏ P ∈ s, _root_.Ideal.absNorm P :=
        _root_.Finset.prod_le_prod (fun _ _ ↦ _root_.Nat.zero_le _) fun P hP ↦
          _root_.TauCeti.one_lt_absNorm_of_prime (hprime P hP)
    _ = _root_.Ideal.absNorm (∏ P ∈ s, P) := (_root_.map_prod _root_.Ideal.absNorm _ _).symm
    _ ≤ _root_.Ideal.absNorm I :=
        _root_.Nat.le_of_dvd (_root_.Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
          (_root_.map_dvd _root_.Ideal.absNorm hprod)

/-- The **crude prime count**: there are at most `[K:ℚ] / log 2 · x log x` height-one primes of
absolute norm at most `x`.

Every such prime divides the ideal generated by `⌊x⌋₊ !`, because a nonzero ideal contains its own
absolute norm; that ideal has absolute norm `(⌊x⌋₊ !) ^ [K:ℚ] ≤ (⌊x⌋₊ ^ ⌊x⌋₊) ^ [K:ℚ]`, and
`TauCeti.two_pow_card_le_absNorm` converts this into a bound on the number of divisors. -/
theorem solution (K : Type*) [_root_.Field K] [_root_.NumberField K] {x : ℝ} (hx : 1 ≤ x) :
    ((_root_.TauCeti.primesLE K x).card : ℝ) * _root_.Real.log 2 ≤ _root_.Module.finrank ℚ K * (x * _root_.Real.log x) := by
  classical
  set M := ⌊x⌋₊
  have hM1 : 1 ≤ M := _root_.Nat.le_floor (by exact_mod_cast hx)
  have hMx : (M : ℝ) ≤ x := _root_.Nat.floor_le (by linarith)
  have hfac : ((_root_.Nat.factorial M) : 𝓞 K) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (_root_.Nat.factorial_ne_zero M)
  have hspan : _root_.Ideal.span {((_root_.Nat.factorial M) : 𝓞 K)} ≠ 0 := by
    simpa [_root_.Ideal.span_singleton_eq_bot] using hfac
  have hcard : 2 ^ (_root_.TauCeti.primesLE K x).card ≤ (_root_.Nat.factorial M) ^ _root_.Module.finrank ℚ K := by
    have himg : ((_root_.TauCeti.primesLE K x).image (fun v ↦ v.asIdeal)).card = (_root_.TauCeti.primesLE K x).card :=
      _root_.Finset.card_image_of_injective _ fun v w h ↦ _root_.IsDedekindDomain.HeightOneSpectrum.ext h
    rw [← himg, ← _root_.NumberField.RingOfIntegers.rank, ← _root_.Ideal.absNorm_span_natCast]
    refine _root_.TauCeti.two_pow_card_le_absNorm hspan ?_ ?_
    · intro P hP
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hP
      exact _root_.Ideal.prime_of_isPrime v.ne_bot v.isPrime
    · intro P hP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
      rw [_root_.Ideal.dvd_iff_le, _root_.Ideal.span_le, _root_.Set.singleton_subset_iff]
      rw [_root_.TauCeti.mem_normLE] at hv
      have hle : _root_.Ideal.absNorm v.asIdeal ≤ M := _root_.Nat.le_floor hv
      obtain ⟨c, hc⟩ := _root_.Nat.dvd_factorial (_root_.Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨v.asIdeal, _root_.mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) hle
      rw [hc]
      push_cast
      exact _root_.Ideal.mul_mem_right _ _ (_root_.Ideal.absNorm_mem v.asIdeal)
  have hlog : ((_root_.TauCeti.primesLE K x).card : ℝ) * _root_.Real.log 2
      ≤ _root_.Module.finrank ℚ K * _root_.Real.log (_root_.Nat.factorial M) := by
    have hcast : (2 : ℝ) ^ (_root_.TauCeti.primesLE K x).card
        ≤ ((_root_.Nat.factorial M) : ℝ) ^ _root_.Module.finrank ℚ K := by
      exact_mod_cast hcard
    have := _root_.Real.log_le_log (by positivity) hcast
    rwa [_root_.Real.log_pow, _root_.Real.log_pow] at this
  refine hlog.trans (_root_.mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hfacle : ((_root_.Nat.factorial M) : ℝ) ≤ (M : ℝ) ^ M := by
    exact_mod_cast _root_.Nat.factorial_le_pow M
  have h1 : _root_.Real.log (_root_.Nat.factorial M) ≤ (M : ℝ) * _root_.Real.log M := by
    have := _root_.Real.log_le_log (by positivity) hfacle
    rwa [_root_.Real.log_pow] at this
  refine h1.trans (_root_.mul_le_mul hMx (_root_.Real.log_le_log (by exact_mod_cast hM1) hMx)
    (_root_.Real.log_nonneg (by exact_mod_cast hM1)) (by linarith))







/-! ### The standard logarithmic weight on the higher prime powers -/





















/-! ### The `O(√x log² x)` estimate -/











/-! ### Other arithmetic weights -/







end TauCeti

end
end
