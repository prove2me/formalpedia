-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_order443_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:11:53.188522+00:00
-- url     : https://prove2.me/submissions/233ab8de-4057-44a3-bf81-797a5d06512f

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 443) = 221 := by
  have hN : (3 : ZMod 443) ^ 221 = 1 := by decide
  have h17 : (3 : ZMod 443) ^ 17 ≠ 1 := by decide
  have h13 : (3 : ZMod 443) ^ 13 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 443) ∣ 221 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 443) ∣ k →
      (3 : ZMod 443) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 443)
    have hcon : (3 : ZMod 443) ^ (orderOf (3 : ZMod 443) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n17 : ¬ orderOf (3 : ZMod 443) ∣ 17 := fun h => mk 17 h h17
  have n13 : ¬ orderOf (3 : ZMod 443) ∣ 13 := fun h => mk 13 h h13
  have hmem : orderOf (3 : ZMod 443) ∈ Nat.divisors 221 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 221 = {1, 13, 17, 221} := by decide
  generalize ho : orderOf (3 : ZMod 443) = o at hdvd n17 n13 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨17, by norm_num⟩ : (1 : Nat) ∣ 17) n17
  · exact absurd (⟨1, by norm_num⟩ : (13 : Nat) ∣ 13) n13
  · exact absurd (⟨1, by norm_num⟩ : (17 : Nat) ∣ 17) n17
  · rfl
