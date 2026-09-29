-- Prove2me | solution 1 for OddPerfectNumber.orders_mod_593_q3_5_19
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T20:17:14.545654+00:00
-- url     : https://prove2.me/submissions/2c8ca17d-955f-4d15-85a4-86ad9e96c930

import Mathlib

theorem solution :
    orderOf (5 : ZMod 593) = 592 ∧
      orderOf (19 : ZMod 593) = 148 := by
  have h5 : orderOf (5 : ZMod 593) = 592 := by
    letI : Fact (Nat.Prime 593) := ⟨by norm_num⟩
    have hne0 : (5 : ZMod 593) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 5 0 593).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (5 : ZMod 593)) (n := 592) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (592 : Nat) = 2 ^ 4 * 37 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow | h37
      · have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow h2pow
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · subst r
          set_option maxRecDepth 100000 in decide
      · have hre : r = 37 :=
          (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 37)).mp h37
        subst r
        set_option maxRecDepth 100000 in decide
  have h19 : orderOf (19 : ZMod 593) = 148 := by
    letI : Fact (Nat.Prime 593) := ⟨by norm_num⟩
    have hne0 : (19 : ZMod 593) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 19 0 593).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (19 : ZMod 593)) (n := 148) (by norm_num)
    · set_option maxRecDepth 100000 in decide
    · intro r hr hdiv
      have hfactor : (148 : Nat) = 2 ^ 2 * 37 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow | h37
      · have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow h2pow
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · subst r
          set_option maxRecDepth 100000 in decide
      · have hre : r = 37 :=
          (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 37)).mp h37
        subst r
        set_option maxRecDepth 100000 in decide
  exact ⟨h5, h19⟩
