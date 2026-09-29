-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_order151_3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T17:19:23.26143+00:00
-- url     : https://prove2.me/submissions/e540966f-fc72-4a27-8f1b-2f2dc1d46d0b

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 151) = 50 := by
  have hN : (3 : ZMod 151) ^ 50 = 1 := by decide
  have hn25 : (3 : ZMod 151) ^ 25 ≠ 1 := by decide
  have hn10 : (3 : ZMod 151) ^ 10 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 151) ∣ 50 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 151) ∣ k → (3 : ZMod 151) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 151)
    have hcon : (3 : ZMod 151) ^ (orderOf (3 : ZMod 151) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n25 : ¬ orderOf (3 : ZMod 151) ∣ 25 := fun h => mk 25 h hn25
  have n10 : ¬ orderOf (3 : ZMod 151) ∣ 10 := fun h => mk 10 h hn10
  have hmem : orderOf (3 : ZMod 151) ∈ Nat.divisors 50 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 50 = {1, 2, 5, 10, 25, 50} := by decide
  generalize ho : orderOf (3 : ZMod 151) = o at hdvd hn25 hn10 n25 n10 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨25, by norm_num⟩ : (1 : Nat) ∣ 25) n25
  · exact absurd (⟨5, by norm_num⟩ : (2 : Nat) ∣ 10) n10
  · exact absurd (⟨5, by norm_num⟩ : (5 : Nat) ∣ 25) n25
  · exact absurd (⟨1, by norm_num⟩ : (10 : Nat) ∣ 10) n10
  · exact absurd (⟨1, by norm_num⟩ : (25 : Nat) ∣ 25) n25
  · rfl
