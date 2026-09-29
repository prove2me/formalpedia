-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order421_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:00:21.173407+00:00
-- url     : https://prove2.me/submissions/34d2e2c4-4678-4603-8e6e-214077f1aa6c

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 421) = 105 := by
  have h105 : (3 : ZMod 421) ^ 105 = 1 := by decide
  have h35 : (3 : ZMod 421) ^ 35 ≠ 1 := by decide
  have h21 : (3 : ZMod 421) ^ 21 ≠ 1 := by decide
  have h15 : (3 : ZMod 421) ^ 15 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 421) ∣ 105 := orderOf_dvd_of_pow_eq_one h105
  have mk : ∀ k : Nat, orderOf (3 : ZMod 421) ∣ k →
      (3 : ZMod 421) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 421)
    have hcon : (3 : ZMod 421) ^ (orderOf (3 : ZMod 421) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n35 : ¬ orderOf (3 : ZMod 421) ∣ 35 := fun h => mk 35 h h35
  have n21 : ¬ orderOf (3 : ZMod 421) ∣ 21 := fun h => mk 21 h h21
  have n15 : ¬ orderOf (3 : ZMod 421) ∣ 15 := fun h => mk 15 h h15
  have hmem : orderOf (3 : ZMod 421) ∈ Nat.divisors 105 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 105 = {1, 3, 5, 7, 15, 21, 35, 105} := by decide
  generalize ho : orderOf (3 : ZMod 421) = o at hdvd n35 n21 n15 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨35, by norm_num⟩ : (1 : Nat) ∣ 35) n35
  · exact absurd (⟨7, by norm_num⟩ : (3 : Nat) ∣ 21) n21
  · exact absurd (⟨7, by norm_num⟩ : (5 : Nat) ∣ 35) n35
  · exact absurd (⟨5, by norm_num⟩ : (7 : Nat) ∣ 35) n35
  · exact absurd (⟨1, by norm_num⟩ : (15 : Nat) ∣ 15) n15
  · exact absurd (⟨1, by norm_num⟩ : (21 : Nat) ∣ 21) n21
  · exact absurd (⟨1, by norm_num⟩ : (35 : Nat) ∣ 35) n35
  · rfl
