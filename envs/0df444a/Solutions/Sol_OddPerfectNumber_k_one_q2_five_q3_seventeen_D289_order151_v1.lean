-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order151_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:52:38.124976+00:00
-- url     : https://prove2.me/submissions/ea51e49b-a8c6-474b-9621-e9f784e3ea9d

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 151) = 50 := by
  have h50 : (3 : ZMod 151) ^ 50 = 1 := by decide
  have h25 : (3 : ZMod 151) ^ 25 ≠ 1 := by decide
  have h10 : (3 : ZMod 151) ^ 10 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 151) ∣ 50 := orderOf_dvd_of_pow_eq_one h50
  have n25 : ¬ orderOf (3 : ZMod 151) ∣ 25 := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hpow := pow_orderOf_eq_one (3 : ZMod 151)
    have hcon : (3 : ZMod 151) ^ (orderOf (3 : ZMod 151) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact h25 hcon
  have n10 : ¬ orderOf (3 : ZMod 151) ∣ 10 := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hpow := pow_orderOf_eq_one (3 : ZMod 151)
    have hcon : (3 : ZMod 151) ^ (orderOf (3 : ZMod 151) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact h10 hcon
  have hmem : orderOf (3 : ZMod 151) ∈ Nat.divisors 50 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 50 = {1, 2, 5, 10, 25, 50} := by decide
  generalize ho : orderOf (3 : ZMod 151) = o at hdvd n25 n10 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨25, by norm_num⟩ : (1 : Nat) ∣ 25) n25
  · exact absurd (⟨5, by norm_num⟩ : (2 : Nat) ∣ 10) n10
  · exact absurd (⟨5, by norm_num⟩ : (5 : Nat) ∣ 25) n25
  · exact absurd (⟨1, by norm_num⟩ : (10 : Nat) ∣ 10) n10
  · exact absurd (⟨1, by norm_num⟩ : (25 : Nat) ∣ 25) n25
  · rfl
