-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_order409_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:12:17.153724+00:00
-- url     : https://prove2.me/submissions/5cfed2cd-c8c4-4fb6-8d92-74053c7a911f

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 409) = 204 := by
  have hN : (3 : ZMod 409) ^ 204 = 1 := by decide
  have h102 : (3 : ZMod 409) ^ 102 ≠ 1 := by decide
  have h68 : (3 : ZMod 409) ^ 68 ≠ 1 := by decide
  have h12 : (3 : ZMod 409) ^ 12 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 409) ∣ 204 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 409) ∣ k →
      (3 : ZMod 409) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 409)
    have hcon : (3 : ZMod 409) ^ (orderOf (3 : ZMod 409) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n102 : ¬ orderOf (3 : ZMod 409) ∣ 102 := fun h => mk 102 h h102
  have n68 : ¬ orderOf (3 : ZMod 409) ∣ 68 := fun h => mk 68 h h68
  have n12 : ¬ orderOf (3 : ZMod 409) ∣ 12 := fun h => mk 12 h h12
  have hmem : orderOf (3 : ZMod 409) ∈ Nat.divisors 204 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 204 = {1, 2, 3, 4, 6, 12, 17, 34, 51, 68, 102, 204} := by decide
  generalize ho : orderOf (3 : ZMod 409) = o at hdvd n102 n68 n12 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨102, by norm_num⟩ : (1 : Nat) ∣ 102) n102
  · exact absurd (⟨51, by norm_num⟩ : (2 : Nat) ∣ 102) n102
  · exact absurd (⟨34, by norm_num⟩ : (3 : Nat) ∣ 102) n102
  · exact absurd (⟨17, by norm_num⟩ : (4 : Nat) ∣ 68) n68
  · exact absurd (⟨17, by norm_num⟩ : (6 : Nat) ∣ 102) n102
  · exact absurd (⟨1, by norm_num⟩ : (12 : Nat) ∣ 12) n12
  · exact absurd (⟨6, by norm_num⟩ : (17 : Nat) ∣ 102) n102
  · exact absurd (⟨3, by norm_num⟩ : (34 : Nat) ∣ 102) n102
  · exact absurd (⟨2, by norm_num⟩ : (51 : Nat) ∣ 102) n102
  · exact absurd (⟨1, by norm_num⟩ : (68 : Nat) ∣ 68) n68
  · exact absurd (⟨1, by norm_num⟩ : (102 : Nat) ∣ 102) n102
  · rfl
