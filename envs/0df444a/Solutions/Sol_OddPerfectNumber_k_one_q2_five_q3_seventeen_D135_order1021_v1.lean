-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_order1021_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:03:49.565603+00:00
-- url     : https://prove2.me/submissions/6db0fad7-1f81-4560-a1ce-b42a352ab4da

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 1021) = 34 := by
  have h34 : (3 : ZMod 1021) ^ 34 = 1 := by decide
  have h17 : (3 : ZMod 1021) ^ 17 ≠ 1 := by decide
  have h2 : (3 : ZMod 1021) ^ 2 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 1021) ∣ 34 := orderOf_dvd_of_pow_eq_one h34
  have mk : ∀ k : Nat, orderOf (3 : ZMod 1021) ∣ k →
      (3 : ZMod 1021) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 1021)
    have hcon : (3 : ZMod 1021) ^ (orderOf (3 : ZMod 1021) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n17 : ¬ orderOf (3 : ZMod 1021) ∣ 17 := fun h => mk 17 h h17
  have n2 : ¬ orderOf (3 : ZMod 1021) ∣ 2 := fun h => mk 2 h h2
  have hmem : orderOf (3 : ZMod 1021) ∈ Nat.divisors 34 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 34 = {1, 2, 17, 34} := by decide
  generalize ho : orderOf (3 : ZMod 1021) = o at hdvd n17 n2 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨17, by norm_num⟩ : (1 : Nat) ∣ 17) n17
  · exact absurd (⟨1, by norm_num⟩ : (2 : Nat) ∣ 2) n2
  · exact absurd (⟨1, by norm_num⟩ : (17 : Nat) ∣ 17) n17
  · rfl
