-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_53_q3_twentythree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:42:08.813275+00:00
-- url     : https://prove2.me/submissions/9cdbbaaa-1017-4447-95d7-d5e1db2f2458

import Mathlib

theorem solution :
    Even (orderOf (3 : ZMod 53)) ∧
      Even (orderOf (5 : ZMod 53)) ∧
      Even (orderOf (23 : ZMod 53)) := by
  have h3 : orderOf (3 : ZMod 53) = 52 := by
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    have hne0 : (3 : ZMod 53) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 3 0 53).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (3 : ZMod 53)) (n := 52) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (52 : Nat) = 4 * 13 := by norm_num
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
        decide
  have h5 : orderOf (5 : ZMod 53) = 52 := by
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    have hne0 : (5 : ZMod 53) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 5 0 53).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (5 : ZMod 53)) (n := 52) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (52 : Nat) = 4 * 13 := by norm_num
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
        decide
  have h23 : orderOf (23 : ZMod 53) = 4 := by
    apply (orderOf_eq_iff (x := (23 : ZMod 53)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n <;> decide
  rw [h3, h5, h23]
  norm_num
