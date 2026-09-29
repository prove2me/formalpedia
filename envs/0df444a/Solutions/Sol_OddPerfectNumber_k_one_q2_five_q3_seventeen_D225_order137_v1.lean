-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_order137_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:11:32.013109+00:00
-- url     : https://prove2.me/submissions/a970a603-dc0f-4075-85c9-70ebd4fa6a39

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 137) = 136 := by
  have hN : (3 : ZMod 137) ^ 136 = 1 := by decide
  have h68 : (3 : ZMod 137) ^ 68 ≠ 1 := by decide
  have h8 : (3 : ZMod 137) ^ 8 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 137) ∣ 136 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 137) ∣ k →
      (3 : ZMod 137) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 137)
    have hcon : (3 : ZMod 137) ^ (orderOf (3 : ZMod 137) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n68 : ¬ orderOf (3 : ZMod 137) ∣ 68 := fun h => mk 68 h h68
  have n8 : ¬ orderOf (3 : ZMod 137) ∣ 8 := fun h => mk 8 h h8
  have hmem : orderOf (3 : ZMod 137) ∈ Nat.divisors 136 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 136 = {1, 2, 4, 8, 17, 34, 68, 136} := by decide
  generalize ho : orderOf (3 : ZMod 137) = o at hdvd n68 n8 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨68, by norm_num⟩ : (1 : Nat) ∣ 68) n68
  · exact absurd (⟨34, by norm_num⟩ : (2 : Nat) ∣ 68) n68
  · exact absurd (⟨17, by norm_num⟩ : (4 : Nat) ∣ 68) n68
  · exact absurd (⟨1, by norm_num⟩ : (8 : Nat) ∣ 8) n8
  · exact absurd (⟨4, by norm_num⟩ : (17 : Nat) ∣ 68) n68
  · exact absurd (⟨2, by norm_num⟩ : (34 : Nat) ∣ 68) n68
  · exact absurd (⟨1, by norm_num⟩ : (68 : Nat) ∣ 68) n68
  · rfl
