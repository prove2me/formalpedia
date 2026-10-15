-- Prove2me | solution 1 for ThreeSum.PrimeChain.prime_divisors_card_le_log
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:02.273474+00:00
-- url     : https://prove2.me/submissions/99612675-6958-4359-a2f3-87978bdde380

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-! # Exact deterministic contraction of the weighted modular score -/

namespace ThreeSum.PrimeChain

open Finset
open scoped BigOperators

variable {ι : Type*}










/-- A nonzero integer cannot have too many distinct prime divisors above y. -/
theorem prime_divisors_card_le_log_sourceProof (C : Finset ℕ) (y : ℕ) (hy : 1 < y)
    (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (z : ℤ) (hz : z ≠ 0) :
    (C.filter fun p => p ∣ z.natAbs).card ≤ Nat.log y z.natAbs := by
  let hits := C.filter fun p => p ∣ z.natAbs
  have hcop : (hits : Set ℕ).Pairwise (fun p q => IsRelPrime p q) := by
    intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime p (mem_filter.mp hp).1)
        (hprime q (mem_filter.mp hq).1)).mpr hne)
  have hdiv : (∏ p ∈ hits, p) ∣ z.natAbs :=
    prod_dvd_of_isRelPrime hcop (fun p hp => (mem_filter.mp hp).2)
  have hlow : y ^ hits.card ≤ ∏ p ∈ hits, p := by
    calc
      y ^ hits.card = ∏ _p ∈ hits, y := by simp
      _ ≤ ∏ p ∈ hits, p := prod_le_prod' (fun p hp => hmin p (mem_filter.mp hp).1)
  have habs : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  exact (Nat.le_log_iff_pow_le hy (by omega)).mpr
    (hlow.trans (Nat.le_of_dvd habs hdiv))








































































































































end ThreeSum.PrimeChain

end


theorem solution : ∀ (C : Finset.{0} Nat) (y : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y →
    (∀ (p : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) C p →
          Nat.Prime p) →
      (∀ (p : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) C p →
            @LE.le.{0} Nat instLENat y p) →
        ∀ (z : Int),
          @Ne.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
            @LE.le.{0} Nat instLENat (@Finset.card.{0} Nat ({p ∈ C | @Dvd.dvd.{0} Nat Nat.instDvd p z.natAbs}))
              (Nat.log y z.natAbs) := by
  exact @ThreeSum.PrimeChain.prime_divisors_card_le_log_sourceProof

#print axioms solution
