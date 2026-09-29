-- Prove2me | solution 1 for OddPerfectNumber.order_q4_587_mod_113_eq_56
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T20:25:09.910709+00:00
-- url     : https://prove2.me/submissions/18b08b0c-8385-4711-bc85-a766cbc73556

import Mathlib

theorem solution : orderOf (587 : ZMod 113) = 56 := by
  letI : Fact (Nat.Prime 113) := ⟨by norm_num⟩
  have hne0 : (587 : ZMod 113) ≠ 0 := by
    intro hz
    have hmod := (ZMod.natCast_eq_natCast_iff' 587 0 113).mp hz
    norm_num at hmod
  apply orderOf_eq_of_pow_and_pow_div_prime (x := (587 : ZMod 113)) (n := 56) (by norm_num)
  · decide
  · intro r hr hdiv
    have hfactor : (56 : Nat) = 2 ^ 3 * 7 := by norm_num
    rw [hfactor] at hdiv
    rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow | h7
    · have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow h2pow
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
      · have hrge : 2 ≤ r := hr.two_le
        omega
      · subst r
        set_option maxRecDepth 100000 in decide
    · have hre : r = 7 :=
        (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 7)).mp h7
      subst r
      set_option maxRecDepth 100000 in decide
