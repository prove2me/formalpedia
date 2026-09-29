-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_193_q3_twentythree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T07:05:45.905267+00:00
-- url     : https://prove2.me/submissions/ddd4d846-11f5-4b95-b828-5a63e956c310

import Mathlib

theorem solution :
    Even (orderOf (3 : ZMod 193)) ∧
    Even (orderOf (5 : ZMod 193)) ∧
    Even (orderOf (23 : ZMod 193)) ∧
    Even (orderOf (97 : ZMod 193)) := by
  have hprime : ∀ {r k : Nat}, r.Prime → r ∣ 2 ^ k → r = 2 := by
    intro r k hr hd
    have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow hd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
    · have := hr.two_le
      omega
    · exact h2
  have h3 : orderOf (3 : ZMod 193) = 16 := by
    letI : Fact (Nat.Prime 193) := ⟨by norm_num⟩
    have hne0 : (3 : ZMod 193) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 3 0 193).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (3 : ZMod 193)) (n := 16) (by norm_num)
    · set_option maxRecDepth 100000 in decide
    · intro r hr hdiv
      have hfactor : (16 : Nat) = 2 ^ 4 := by norm_num
      rw [hfactor] at hdiv
      have hre : r = 2 := hprime hr hdiv
      subst r
      set_option maxRecDepth 100000 in decide
  have h5 : orderOf (5 : ZMod 193) = 192 := by
    letI : Fact (Nat.Prime 193) := ⟨by norm_num⟩
    have hne0 : (5 : ZMod 193) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 5 0 193).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (5 : ZMod 193)) (n := 192) (by norm_num)
    · exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (192 : Nat) = 2 ^ 6 * 3 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow | h3
      · have hre : r = 2 := hprime hr h2pow
        subst r
        set_option maxRecDepth 100000 in decide
      · have hre : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h3
        subst r
        set_option maxRecDepth 100000 in decide
  have h23 : orderOf (23 : ZMod 193) = 32 := by
    letI : Fact (Nat.Prime 193) := ⟨by norm_num⟩
    have hne0 : (23 : ZMod 193) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 23 0 193).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (23 : ZMod 193)) (n := 32) (by norm_num)
    · set_option maxRecDepth 100000 in decide
    · intro r hr hdiv
      have hfactor : (32 : Nat) = 2 ^ 5 := by norm_num
      rw [hfactor] at hdiv
      have hre : r = 2 := hprime hr hdiv
      subst r
      set_option maxRecDepth 100000 in decide
  have h97 : orderOf (97 : ZMod 193) = 96 := by
    letI : Fact (Nat.Prime 193) := ⟨by norm_num⟩
    have hne0 : (97 : ZMod 193) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 97 0 193).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (97 : ZMod 193)) (n := 96) (by norm_num)
    · set_option maxRecDepth 100000 in decide
    · intro r hr hdiv
      have hfactor : (96 : Nat) = 2 ^ 5 * 3 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow | h3
      · have hre : r = 2 := hprime hr h2pow
        subst r
        set_option maxRecDepth 100000 in decide
      · have hre : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h3
        subst r
        set_option maxRecDepth 100000 in decide
  rw [h3, h5, h23, h97]
  norm_num
