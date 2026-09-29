-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_order239_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:11:36.829332+00:00
-- url     : https://prove2.me/submissions/1c102054-5863-4e22-bf7b-358a39b5e1f5

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 239) = 119 := by
  have hN : (3 : ZMod 239) ^ 119 = 1 := by decide
  have h17 : (3 : ZMod 239) ^ 17 ≠ 1 := by decide
  have h7 : (3 : ZMod 239) ^ 7 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 239) ∣ 119 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 239) ∣ k →
      (3 : ZMod 239) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 239)
    have hcon : (3 : ZMod 239) ^ (orderOf (3 : ZMod 239) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n17 : ¬ orderOf (3 : ZMod 239) ∣ 17 := fun h => mk 17 h h17
  have n7 : ¬ orderOf (3 : ZMod 239) ∣ 7 := fun h => mk 7 h h7
  have hmem : orderOf (3 : ZMod 239) ∈ Nat.divisors 119 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 119 = {1, 7, 17, 119} := by decide
  generalize ho : orderOf (3 : ZMod 239) = o at hdvd n17 n7 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨17, by norm_num⟩ : (1 : Nat) ∣ 17) n17
  · exact absurd (⟨1, by norm_num⟩ : (7 : Nat) ∣ 7) n7
  · exact absurd (⟨1, by norm_num⟩ : (17 : Nat) ∣ 17) n17
  · rfl
