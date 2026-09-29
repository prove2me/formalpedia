-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order181_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:54:29.63081+00:00
-- url     : https://prove2.me/submissions/4159b389-8a68-4d06-80f6-a30cdc9eea1c

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 181) = 45 := by
  have h45 : (3 : ZMod 181) ^ 45 = 1 := by decide
  have h15 : (3 : ZMod 181) ^ 15 ≠ 1 := by decide
  have h9 : (3 : ZMod 181) ^ 9 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 181) ∣ 45 := orderOf_dvd_of_pow_eq_one h45
  have n15 : ¬ orderOf (3 : ZMod 181) ∣ 15 := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hpow := pow_orderOf_eq_one (3 : ZMod 181)
    have hcon : (3 : ZMod 181) ^ (orderOf (3 : ZMod 181) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact h15 hcon
  have n9 : ¬ orderOf (3 : ZMod 181) ∣ 9 := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hpow := pow_orderOf_eq_one (3 : ZMod 181)
    have hcon : (3 : ZMod 181) ^ (orderOf (3 : ZMod 181) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact h9 hcon
  have hmem : orderOf (3 : ZMod 181) ∈ Nat.divisors 45 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 45 = {1, 3, 5, 9, 15, 45} := by decide
  generalize ho : orderOf (3 : ZMod 181) = o at hdvd n15 n9 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨15, by norm_num⟩ : (1 : Nat) ∣ 15) n15
  · exact absurd (⟨5, by norm_num⟩ : (3 : Nat) ∣ 15) n15
  · exact absurd (⟨3, by norm_num⟩ : (5 : Nat) ∣ 15) n15
  · exact absurd (⟨1, by norm_num⟩ : (9 : Nat) ∣ 9) n9
  · exact absurd (⟨1, by norm_num⟩ : (15 : Nat) ∣ 15) n15
  · rfl
