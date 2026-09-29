-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order271_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:00:12.271843+00:00
-- url     : https://prove2.me/submissions/3bf0db9f-a30d-41ef-a167-8f05b6244f7e

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 271) = 30 := by
  have h30 : (3 : ZMod 271) ^ 30 = 1 := by decide
  have h15 : (3 : ZMod 271) ^ 15 ≠ 1 := by decide
  have h10 : (3 : ZMod 271) ^ 10 ≠ 1 := by decide
  have h6 : (3 : ZMod 271) ^ 6 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 271) ∣ 30 := orderOf_dvd_of_pow_eq_one h30
  have mk : ∀ k : Nat, orderOf (3 : ZMod 271) ∣ k →
      (3 : ZMod 271) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 271)
    have hcon : (3 : ZMod 271) ^ (orderOf (3 : ZMod 271) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n15 : ¬ orderOf (3 : ZMod 271) ∣ 15 := fun h => mk 15 h h15
  have n10 : ¬ orderOf (3 : ZMod 271) ∣ 10 := fun h => mk 10 h h10
  have n6 : ¬ orderOf (3 : ZMod 271) ∣ 6 := fun h => mk 6 h h6
  have hmem : orderOf (3 : ZMod 271) ∈ Nat.divisors 30 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 30 = {1, 2, 3, 5, 6, 10, 15, 30} := by decide
  generalize ho : orderOf (3 : ZMod 271) = o at hdvd n15 n10 n6 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨15, by norm_num⟩ : (1 : Nat) ∣ 15) n15
  · exact absurd (⟨5, by norm_num⟩ : (2 : Nat) ∣ 10) n10
  · exact absurd (⟨5, by norm_num⟩ : (3 : Nat) ∣ 15) n15
  · exact absurd (⟨3, by norm_num⟩ : (5 : Nat) ∣ 15) n15
  · exact absurd (⟨1, by norm_num⟩ : (6 : Nat) ∣ 6) n6
  · exact absurd (⟨1, by norm_num⟩ : (10 : Nat) ∣ 10) n10
  · exact absurd (⟨1, by norm_num⟩ : (15 : Nat) ∣ 15) n15
  · rfl
