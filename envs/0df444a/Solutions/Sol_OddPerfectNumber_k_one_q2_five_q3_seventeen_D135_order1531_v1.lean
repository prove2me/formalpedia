-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_order1531_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:03:53.949284+00:00
-- url     : https://prove2.me/submissions/8e425298-abe9-4172-b5cf-6ffe82cce017

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 1531) = 170 := by
  have h170 : (3 : ZMod 1531) ^ 170 = 1 := by decide
  have h85 : (3 : ZMod 1531) ^ 85 ≠ 1 := by decide
  have h34 : (3 : ZMod 1531) ^ 34 ≠ 1 := by decide
  have h10 : (3 : ZMod 1531) ^ 10 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 1531) ∣ 170 := orderOf_dvd_of_pow_eq_one h170
  have mk : ∀ k : Nat, orderOf (3 : ZMod 1531) ∣ k →
      (3 : ZMod 1531) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 1531)
    have hcon : (3 : ZMod 1531) ^ (orderOf (3 : ZMod 1531) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n85 : ¬ orderOf (3 : ZMod 1531) ∣ 85 := fun h => mk 85 h h85
  have n34 : ¬ orderOf (3 : ZMod 1531) ∣ 34 := fun h => mk 34 h h34
  have n10 : ¬ orderOf (3 : ZMod 1531) ∣ 10 := fun h => mk 10 h h10
  have hmem : orderOf (3 : ZMod 1531) ∈ Nat.divisors 170 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 170 = {1, 2, 5, 10, 17, 34, 85, 170} := by decide
  generalize ho : orderOf (3 : ZMod 1531) = o at hdvd n85 n34 n10 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨85, by norm_num⟩ : (1 : Nat) ∣ 85) n85
  · exact absurd (⟨17, by norm_num⟩ : (2 : Nat) ∣ 34) n34
  · exact absurd (⟨17, by norm_num⟩ : (5 : Nat) ∣ 85) n85
  · exact absurd (⟨1, by norm_num⟩ : (10 : Nat) ∣ 10) n10
  · exact absurd (⟨5, by norm_num⟩ : (17 : Nat) ∣ 85) n85
  · exact absurd (⟨1, by norm_num⟩ : (34 : Nat) ∣ 34) n34
  · exact absurd (⟨1, by norm_num⟩ : (85 : Nat) ∣ 85) n85
  · rfl
