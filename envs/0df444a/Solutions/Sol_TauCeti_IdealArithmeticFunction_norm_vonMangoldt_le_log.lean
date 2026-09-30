-- Prove2me | solution 1 for TauCeti.IdealArithmeticFunction.norm_vonMangoldt_le_log
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:55.333185+00:00
-- url     : https://prove2.me/submissions/bbe397d4-d82a-4bad-9d3c-ddcfececb55f

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

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
end TauCeti
section TauCeti
open TauCeti

open _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of a prime ideal is greater than one. -/
theorem TauCeti.one_lt_absNorm_of_prime {P : _root_.Ideal (𝓞 K)} (hP : _root_.Prime P) :
    1 < _root_.Ideal.absNorm P := by
  rw [_root_.Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero,
    Ideal.absNorm_eq_one_iff.not.mpr fun htop ↦
      hP.not_isUnit (Ideal.isUnit_iff.mpr htop)⟩

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction





/-- The value of the ideal von Mangoldt function at a positive power of a prime ideal.  This is the
choice-free characterization of `vonMangoldt` on its support. -/
theorem TauCeti.IdealArithmeticFunction.vonMangoldt_apply_of_eq_prime_pow {A : (_root_.Ideal (𝓞 K))⁰} {P : _root_.Ideal (𝓞 K)}
    (hP : _root_.Prime P) {n : ℕ} (hn : 0 < n) (hpow : P ^ n = (A : _root_.Ideal (𝓞 K))) :
    (_root_.TauCeti.IdealArithmeticFunction.vonMangoldt : _root_.TauCeti.IdealArithmeticFunction K) A = _root_.Real.log (_root_.Ideal.absNorm P) := by
  have hA : _root_.IsPrimePow (A : _root_.Ideal (𝓞 K)) := ⟨P, n, hP, hn, hpow⟩
  have hchosen : hA.choose = P := by
    exact _root_.eq_of_prime_pow_eq hA.choose_spec.choose_spec.1 hP
      hA.choose_spec.choose_spec.2.1 (hA.choose_spec.choose_spec.2.2.trans hpow.symm)
  rw [_root_.TauCeti.IdealArithmeticFunction.vonMangoldt, _root_.dif_pos hA, hchosen]





/-- The ideal von Mangoldt function vanishes away from prime powers. -/
@[simp]
theorem TauCeti.IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow {A : (_root_.Ideal (𝓞 K))⁰}
    (hA : ¬ _root_.IsPrimePow (A : _root_.Ideal (𝓞 K))) :
    (_root_.TauCeti.IdealArithmeticFunction.vonMangoldt : _root_.TauCeti.IdealArithmeticFunction K) A = 0 := by
  simp [_root_.TauCeti.IdealArithmeticFunction.vonMangoldt, hA]











/-- **The von Mangoldt function is bounded by the logarithm of the norm.** On a power `P ^ n` its
value is `log N(P)`, and the norm of the ideal is `N(P) ^ n` with `n ≥ 1`, so the bound is the
inequality `log N(P) ≤ n log N(P)`; off the prime powers the function vanishes and the logarithm is
still nonnegative.

This is the ideal analogue of `ArithmeticFunction.vonMangoldt_le_log`, and it is what compares a
von Mangoldt weighted ideal term against the `log N(I)` weighted terms of
`TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`. -/
theorem solution (A : (_root_.Ideal (𝓞 K))⁰) :
    ‖(_root_.TauCeti.IdealArithmeticFunction.vonMangoldt : _root_.TauCeti.IdealArithmeticFunction K) A‖
      ≤ _root_.Real.log (_root_.Ideal.absNorm (A : _root_.Ideal (𝓞 K))) := by
  have hA1 : (1 : ℝ) ≤ _root_.Ideal.absNorm (A : _root_.Ideal (𝓞 K)) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (_root_.Ideal.absNorm_ne_zero_of_nonZeroDivisors A)
  by_cases hA : _root_.IsPrimePow (A : _root_.Ideal (𝓞 K))
  · obtain ⟨P, n, hP, hn, hpow⟩ := hA
    have hP1 : (1 : ℝ) ≤ _root_.Ideal.absNorm P := by
      exact_mod_cast (_root_.TauCeti.one_lt_absNorm_of_prime hP).le
    have hlog : 0 ≤ _root_.Real.log (_root_.Ideal.absNorm P) := _root_.Real.log_nonneg hP1
    rw [_root_.TauCeti.IdealArithmeticFunction.vonMangoldt_apply_of_eq_prime_pow hP hn hpow, _root_.Complex.norm_real, _root_.Real.norm_eq_abs,
      _root_.abs_of_nonneg hlog, ← hpow, _root_.map_pow, _root_.Nat.cast_pow, _root_.Real.log_pow]
    exact _root_.le_mul_of_one_le_left hlog (by exact_mod_cast hn)
  · rw [_root_.TauCeti.IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hA, _root_.norm_zero]
    exact _root_.Real.log_nonneg hA1











end IdealArithmeticFunction

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight





end MultiplicativeIdealWeight

end TauCeti

end
end
