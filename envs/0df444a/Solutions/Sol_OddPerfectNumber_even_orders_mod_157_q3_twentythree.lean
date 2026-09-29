-- Prove2me | solution 1 for OddPerfectNumber.even_orders_mod_157_q3_twentythree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T07:21:28.347901+00:00
-- url     : https://prove2.me/submissions/6d86a9ca-0539-414c-9fb0-b0c4db964202

import Mathlib

theorem solution :
    Even (orderOf (3 : ZMod 157)) ∧
    Even (orderOf (5 : ZMod 157)) ∧
    Even (orderOf (23 : ZMod 157)) ∧
    Even (orderOf (79 : ZMod 157)) := by
  have hprime : ∀ {r k : Nat}, r.Prime → r ∣ 2 ^ k → r = 2 := by
    intro r k hr hd
    have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow hd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hr2 with h1 | h2
    · have := hr.two_le
      omega
    · exact h2
  have hprime_two : ∀ {r : Nat}, r.Prime → r ∣ 2 → r = 2 := by
    intro r hr hd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd with h1 | h2
    · have := hr.two_le
      omega
    · exact h2
  have h3 : orderOf (3 : ZMod 157) = 78 := by
    letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
    have hne0 : (3 : ZMod 157) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 3 0 157).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (3 : ZMod 157)) (n := 78) (by norm_num)
    · set_option maxRecDepth 100000 in decide
    · intro r hr hdiv
      have hfactor : (78 : Nat) = 2 * 3 * 13 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h23 | h13
      · rcases (Nat.Prime.dvd_mul hr).mp h23 with h2 | h3
        · have hre : r = 2 := hprime_two hr h2
          subst r
          set_option maxRecDepth 100000 in decide
        · have hre : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h3
          subst r
          set_option maxRecDepth 100000 in decide
      · have hre : r = 13 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h13
        subst r
        set_option maxRecDepth 100000 in decide
  have h5 : orderOf (5 : ZMod 157) = 156 := by
    letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
    have hne0 : (5 : ZMod 157) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 5 0 157).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (5 : ZMod 157)) (n := 156) (by norm_num)
    · set_option maxRecDepth 100000 in
        exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (156 : Nat) = 2 ^ 2 * 3 * 13 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow3 | h13
      · rcases (Nat.Prime.dvd_mul hr).mp h2pow3 with h2pow | h3
        · have hre : r = 2 := hprime hr h2pow
          subst r
          set_option maxRecDepth 100000 in decide
        · have hre : r = 3 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h3
          subst r
          set_option maxRecDepth 100000 in decide
      · have hre : r = 13 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h13
        subst r
        set_option maxRecDepth 100000 in decide
  have h23 : orderOf (23 : ZMod 157) = 52 := by
    letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
    have hne0 : (23 : ZMod 157) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 23 0 157).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (23 : ZMod 157)) (n := 52) (by norm_num)
    · set_option maxRecDepth 100000 in
        exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (52 : Nat) = 2 ^ 2 * 13 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow | h13
      · have hre : r = 2 := hprime hr h2pow
        subst r
        set_option maxRecDepth 100000 in decide
      · have hre : r = 13 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h13
        subst r
        set_option maxRecDepth 100000 in decide
  have h79 : orderOf (79 : ZMod 157) = 52 := by
    letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
    have hne0 : (79 : ZMod 157) ≠ 0 := by
      intro hz
      have hmod := (ZMod.natCast_eq_natCast_iff' 79 0 157).mp hz
      norm_num at hmod
    apply orderOf_eq_of_pow_and_pow_div_prime (x := (79 : ZMod 157)) (n := 52) (by norm_num)
    · set_option maxRecDepth 100000 in
        exact ZMod.pow_card_sub_one_eq_one hne0
    · intro r hr hdiv
      have hfactor : (52 : Nat) = 2 ^ 2 * 13 := by norm_num
      rw [hfactor] at hdiv
      rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2pow | h13
      · have hre : r = 2 := hprime hr h2pow
        subst r
        set_option maxRecDepth 100000 in decide
      · have hre : r = 13 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h13
        subst r
        set_option maxRecDepth 100000 in decide
  exact ⟨by simpa [h3] using (show Even 78 by norm_num),
    by simpa [h5] using (show Even 156 by norm_num),
    by simpa [h23] using (show Even 52 by norm_num),
    by simpa [h79] using (show Even 52 by norm_num)⟩
