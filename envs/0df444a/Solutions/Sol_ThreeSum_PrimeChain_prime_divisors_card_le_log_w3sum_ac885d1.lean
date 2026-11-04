-- Prove2me | solution 1 for ThreeSum.PrimeChain.prime_divisors_card_le_log_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:10.77863+00:00
-- url     : https://prove2.me/submissions/7fb71db8-f933-4374-9fe2-8bc00339b443

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}
namespace ThreeSum.PrimeChain
theorem _root_.solution (C : Finset ℕ) (y : ℕ) (hy : 1 < y)
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
