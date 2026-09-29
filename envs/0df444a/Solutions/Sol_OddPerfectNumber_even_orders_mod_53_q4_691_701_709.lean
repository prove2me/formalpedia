-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_53_q4_691_701_709
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:55:29.967338+00:00
-- url     : https://prove2.me/submissions/8526c003-3984-49b7-8820-913c7756a08a

import Mathlib

theorem solution :
    Even (orderOf (691 : ZMod 53)) ∧
      Even (orderOf (701 : ZMod 53)) ∧
      Even (orderOf (709 : ZMod 53)) := by
  have h691 : orderOf (691 : ZMod 53) = 52 := by
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    have hne0 : (691 : ZMod 53) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 691 0 53).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (691 : ZMod 53)) (n := 52) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (52 : Nat) = 2 ^ 2 * 13 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h4 | h13
      · have h4pow : r ∣ 2 ^ 2 := by simpa using h4
        have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow h4pow
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · subst r
          set_option maxRecDepth 100000 in decide
      · have hre : r = 13 :=
          (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 13)).mp h13
        subst r
        set_option maxRecDepth 100000 in decide
  have h701 : orderOf (701 : ZMod 53) = 52 := by
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    have hne0 : (701 : ZMod 53) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 701 0 53).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (701 : ZMod 53)) (n := 52) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (52 : Nat) = 2 ^ 2 * 13 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h4 | h13
      · have h4pow : r ∣ 2 ^ 2 := by simpa using h4
        have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow h4pow
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · subst r
          set_option maxRecDepth 100000 in decide
      · have hre : r = 13 :=
          (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 13)).mp h13
        subst r
        set_option maxRecDepth 100000 in decide
  have h709 : orderOf (709 : ZMod 53) = 52 := by
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    have hne0 : (709 : ZMod 53) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 709 0 53).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (709 : ZMod 53)) (n := 52) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (52 : Nat) = 2 ^ 2 * 13 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h4 | h13
      · have h4pow : r ∣ 2 ^ 2 := by simpa using h4
        have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow h4pow
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
        · have hrge : 2 ≤ r := hr.two_le
          omega
        · subst r
          set_option maxRecDepth 100000 in decide
      · have hre : r = 13 :=
          (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 13)).mp h13
        subst r
        set_option maxRecDepth 100000 in decide
  rw [h691, h701, h709]
  norm_num
