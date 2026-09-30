-- Prove2me | solution 1 for TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:26:36.716828+00:00
-- url     : https://prove2.me/submissions/0f849f7a-b390-4d28-a929-836c1483eb94

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.RamificationInertia.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ramification indices in finite flat towers

This file records consequences of the fundamental identity for ramification and inertia in a finite
flat extension of domains. The number of primes above a prime and each prime's contribution are at
most the rank of the extension. Ramification also cancels in a tower when the absolute ramification
index at the top equals the absolute ramification index at the intermediate prime: multiplicativity
then forces the relative ramification index to be one.

The cancellation result is the local step used in the finite-place half of the genus-field
construction. At a rational prime dividing a prime discriminant, both the quadratic base and the
prime-discriminant compositum have absolute ramification index two; cancellation then shows that
the compositum is unramified over the quadratic base.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_le_finrank`: the number of primes above a prime is
  at most the rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank`: the contribution of one
  prime to the fundamental identity is at most the rank of the extension.
* `TauCeti.RamificationInertia.ramificationIdx_le_finrank`: a ramification index is at most the
  rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_eq_one_of_eq_ramificationIdx`: equal absolute
  ramification indices at two levels of a tower force relative ramification index one.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_eq_ramificationIdx`: if that equality
  holds at every prime above an intermediate prime, then the intermediate prime is unramified in
  the top ring.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le`: it suffices to bound
  every absolute ramification index upstairs by the intermediate absolute ramification index.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one`: a
  transverse unramified subextension of sufficiently small relative degree supplies that bound.
* `TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn`: unramifiedness over the
  base descends from an integral extension to the subring below it, for `S` integral and
  torsion-free over the Dedekind domain `R`, with `R` and `S` both essentially of finite type over
  the base `A` and `A ≤ R ≤ S` a scalar tower. The base ring and the ideal are arbitrary.
-/

 section

open Ideal Module

namespace TauCeti.RamificationInertia
end TauCeti.RamificationInertia
section TauCeti.RamificationInertia
open TauCeti TauCeti.RamificationInertia

section Bounds

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]



/-- **One prime's contribution to the fundamental identity is at most the extension rank.**
For a prime `q` of `S` above a prime `p` of `R`, the product of its ramification index and inertia
degree is at most `Module.finrank R S`. -/
theorem solution (p : _root_.Ideal R) [p.IsPrime]
    (q : _root_.Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx R * q.inertiaDeg R ≤ _root_.Module.finrank R S := by
  classical
  have : _root_.Fintype (p.primesOver S) := (_root_.Algebra.QuasiFinite.finite_primesOver p).fintype
  let q' : p.primesOver S := ⟨q, _root_.inferInstance, _root_.inferInstance⟩
  calc
    q.ramificationIdx R * q.inertiaDeg R =
        q'.1.ramificationIdx R * q'.1.inertiaDeg R := _root_.rfl
    _ ≤ ∑ Q : p.primesOver S, Q.1.ramificationIdx R * Q.1.inertiaDeg R :=
      _root_.Finset.single_le_sum
        (f := fun Q : p.primesOver S => Q.1.ramificationIdx R * Q.1.inertiaDeg R)
        (fun _ _ => _root_.Nat.zero_le _) (_root_.Finset.mem_univ q')
    _ = _root_.Module.finrank R S := _root_.Ideal.sum_ramification_inertia_eq_finrank p S



end Bounds

section Tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Module.Finite R S] [Module.Flat S T]









end Tower

section Descent

variable {A R S : Type*} [CommRing A] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
  [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [Algebra.IsIntegral R S]
  [Module.IsTorsionFree R S] [Algebra.EssFiniteType A R] [Algebra.EssFiniteType A S]

-- Source. Recovered from the retired PR #5538, at commit
-- 70421db267d9bd6252256f873d27e99e739a931c.



end Descent

end TauCeti.RamificationInertia

end
end
