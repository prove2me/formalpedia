-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order61_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:53:04.51135+00:00
-- url     : https://prove2.me/submissions/a1c31287-3f76-42b8-bbf7-b36c1e7062e6

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 61) = 10 := by
  have h10 : (3 : ZMod 61) ^ 10 = 1 := by decide
  have h5 : (3 : ZMod 61) ^ 5 ≠ 1 := by decide
  have h2 : (3 : ZMod 61) ^ 2 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 61) ∣ 10 := orderOf_dvd_of_pow_eq_one h10
  have n5 : ¬ orderOf (3 : ZMod 61) ∣ 5 := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hpow := pow_orderOf_eq_one (3 : ZMod 61)
    have hcon : (3 : ZMod 61) ^ (orderOf (3 : ZMod 61) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact h5 hcon
  have n2 : ¬ orderOf (3 : ZMod 61) ∣ 2 := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hpow := pow_orderOf_eq_one (3 : ZMod 61)
    have hcon : (3 : ZMod 61) ^ (orderOf (3 : ZMod 61) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact h2 hcon
  have hmem : orderOf (3 : ZMod 61) ∈ Nat.divisors 10 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 10 = {1, 2, 5, 10} := by decide
  generalize ho : orderOf (3 : ZMod 61) = o at hdvd n5 n2 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨5, by norm_num⟩ : (1 : Nat) ∣ 5) n5
  · exact absurd (⟨1, by norm_num⟩ : (2 : Nat) ∣ 2) n2
  · exact absurd (⟨1, by norm_num⟩ : (5 : Nat) ∣ 5) n5
  · rfl
