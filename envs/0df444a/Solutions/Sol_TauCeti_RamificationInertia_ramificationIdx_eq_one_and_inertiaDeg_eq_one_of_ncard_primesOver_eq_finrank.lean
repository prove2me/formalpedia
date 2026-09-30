-- Prove2me | solution 1 for TauCeti.RamificationInertia.ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:35.278979+00:00
-- url     : https://prove2.me/submissions/cb5e3c1d-784f-4b06-86fa-c3a15fb0ddf3

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RamificationInertia.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complete splitting is trivial ramification and inertia

This file records the non-Galois counting criterion for primes in finite flat extensions of
domains: a prime has as many primes above it as the degree allows exactly when every one of them
is unramified with trivial residue extension.

The Galois form, where the count is compared with the order of the Galois group, is in
`TauCeti/NumberTheory/RamificationInertia/Galois.lean`. No Galois hypothesis is needed here:
the fundamental identity alone forces each summand `e * f` down to `1`.

## Main results

* `ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank` — a maximal count
  of primes above `P` makes `e = f = 1` at each of them.
* `Ideal.ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one` —
  conversely, `e = f = 1` at every prime above `P` makes the count maximal.
* `bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank` — for `P` maximal, the same count
  makes the residue map `R ⧸ P → S ⧸ Q` bijective.

## Provenance

Built directly on Mathlib's fundamental identity for finite flat extensions of domains
(`Ideal.sum_ramification_inertia_eq_finrank`). The residue-field consequence additionally uses
Mathlib's identification of the inertia degree with the rank of the residue extension
(`Ideal.inertiaDeg'_algebraMap`) and its characterisation of rank-one algebras over a field
(`Algebra.finrank_eq_one_iff_bijective_algebraMap`).
-/

 section

open Ideal Module

namespace TauCeti.RamificationInertia
end TauCeti.RamificationInertia
section TauCeti.RamificationInertia
open TauCeti TauCeti.RamificationInertia

/-- **A maximal count of primes above `P` forces `e = f = 1`.** If the number of primes of `S`
lying over a prime `P` of `R` equals the rank of `S` over `R`, then each such prime is unramified
over `P` and has trivial inertia degree. No Galois hypothesis is needed. -/
theorem solution
    {R S : Type*} [_root_.CommRing R] [_root_.IsDomain R] [_root_.CommRing S] [_root_.Algebra R S] [_root_.Module.Finite R S]
    [_root_.Module.Flat R S] (P : _root_.Ideal R) [P.IsPrime] (Q : _root_.Ideal S)
    [Q.IsPrime] [Q.LiesOver P] (hsplit : (P.primesOver S).ncard = _root_.Module.finrank R S) :
    Q.ramificationIdx R = 1 ∧ Q.inertiaDeg R = 1 := by
  have hfin : _root_.Fintype (P.primesOver S) := (_root_.Algebra.QuasiFinite.finite_primesOver P).fintype
  have hsum := _root_.Ideal.sum_ramification_inertia_eq_finrank (R := R) (S := S) (p := P)
  have hcard : _root_.Fintype.card (P.primesOver S) = _root_.Module.finrank R S := by
    rw [← hsplit, _root_.Set.ncard_eq_toFinset_card']
    simp
  -- the fundamental identity writes the rank as `∑ e * f` over the primes above `P`; each
  -- summand is at least `1`, and their number already accounts for the whole rank
  have hone : ∀ q ∈ (_root_.Finset.univ : _root_.Finset (P.primesOver S)),
      1 ≤ q.1.ramificationIdx R * q.1.inertiaDeg R := fun q _ =>
    Nat.one_le_iff_ne_zero.mpr
      (_root_.Nat.mul_ne_zero (_root_.Ideal.ramificationIdx_pos (R := R) (q := q.1)).ne'
        (_root_.Ideal.inertiaDeg_pos (R := R) (q := q.1)).ne')
  have hEqSum : ∑ _q : P.primesOver S, (1 : ℕ) =
      ∑ q : P.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R := by
    rw [hsum, _root_.Finset.sum_const, _root_.Finset.card_univ, _root_.smul_eq_mul, _root_.mul_one, hcard]
  have hQ : (⟨Q, ⟨_root_.inferInstance, _root_.inferInstance⟩⟩ : P.primesOver S) ∈ _root_.Finset.univ :=
    _root_.Finset.mem_univ _
  have := (_root_.Finset.sum_eq_sum_iff_of_le hone).mp hEqSum _ hQ
  exact ⟨_root_.Nat.eq_one_of_mul_eq_one_right this.symm, _root_.Nat.eq_one_of_mul_eq_one_left this.symm⟩

end TauCeti.RamificationInertia

open TauCeti.RamificationInertia

namespace Ideal
end Ideal
section Ideal
open Ideal



end Ideal

namespace TauCeti.RamificationInertia
end TauCeti.RamificationInertia
section TauCeti.RamificationInertia
open TauCeti TauCeti.RamificationInertia



end TauCeti.RamificationInertia

end
end
