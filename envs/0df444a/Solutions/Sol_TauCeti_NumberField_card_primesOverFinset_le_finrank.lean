-- Prove2me | solution 1 for TauCeti.NumberField.card_primesOverFinset_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:23.270473+00:00
-- url     : https://prove2.me/submissions/2e1a6176-19d7-46ca-8e2c-009f1ff6a9a3

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Prime ideals of rings of integers

This file records general utilities for the prime ideals of a number field above a rational
prime: packaging them as non-zero-divisors so that their classes can be taken with
`ClassGroup.mk0`, counting them, and factoring an unramified rational prime into them.

## Main results

* `NumberField.mem_nonZeroDivisors_of_prime_of_liesOver`: a prime ideal above a rational prime is
  a non-zero-divisor in the ideal monoid.
* `NumberField.exists_primeIdealFamily`: a finite set of rational primes admits a family of prime
  ideals above it, packaged for `ClassGroup.mk0`.
* `TauCeti.NumberField.card_primesOverFinset_le_finrank`: at most `[K : ℚ]` primes of `𝓞 K`
  lie over a nonzero prime of `ℤ`.
* `TauCeti.NumberField.span_natCast_eq_prod_primesOverFinset`: a rational prime unramified in
  `K` generates the squarefree product of the primes of `𝓞 K` above it.
-/

 section

open NumberField Ideal
open scoped NumberField nonZeroDivisors

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K : Type*} [Field K] [NumberField K]





end NumberField

namespace TauCeti.NumberField
end TauCeti.NumberField
section TauCeti.NumberField
open TauCeti TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- At most `[K : ℚ]` primes of `𝓞 K` lie over a given nonzero prime of `ℤ`, since each
contributes a positive `ramificationIdx * inertiaDeg` to the fundamental identity. -/
theorem solution {p : _root_.Ideal ℤ} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (_root_.IsDedekindDomain.primesOverFinset p (𝓞 K)).card ≤ _root_.Module.finrank ℚ K :=
  calc
    (_root_.IsDedekindDomain.primesOverFinset p (𝓞 K)).card = ∑ _q : p.primesOver (𝓞 K), 1 := by
      rw [_root_.Finset.sum_const, _root_.smul_eq_mul, _root_.mul_one, _root_.Finset.card_univ,
        ← _root_.Nat.card_eq_fintype_card, _root_.Nat.card_coe_set_eq,
        ← _root_.IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 K), _root_.Set.ncard_coe_finset]
    _ ≤ ∑ q : p.primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
      _root_.Finset.sum_le_sum fun q _ => Nat.one_le_iff_ne_zero.mpr
        (_root_.Nat.mul_ne_zero (_root_.Ideal.ramificationIdx_pos q.1 ℤ).ne'
          (_root_.Ideal.inertiaDeg_pos q.1 ℤ).ne')
    _ = _root_.Module.finrank ℤ (𝓞 K) := _root_.Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)
    _ = _root_.Module.finrank ℚ K := _root_.NumberField.RingOfIntegers.rank K



end TauCeti.NumberField

end
end
