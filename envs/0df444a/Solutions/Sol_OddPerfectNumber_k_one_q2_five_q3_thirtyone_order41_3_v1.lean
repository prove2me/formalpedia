-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_order41_3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T12:35:53.115134+00:00
-- url     : https://prove2.me/submissions/aa2c0904-031c-49b4-b472-ee2e3ac36724

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 41) = 8 := by
  have hN : (3 : ZMod 41) ^ 8 = 1 := by decide
  have hn4 : (3 : ZMod 41) ^ 4 ≠ 1 := by decide
  have hn2 : (3 : ZMod 41) ^ 2 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 41) ∣ 8 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 41) ∣ k → (3 : ZMod 41) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 41)
    have hcon : (3 : ZMod 41) ^ (orderOf (3 : ZMod 41) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n4 : ¬ orderOf (3 : ZMod 41) ∣ 4 := fun h => mk 4 h hn4
  have n2 : ¬ orderOf (3 : ZMod 41) ∣ 2 := fun h => mk 2 h hn2
  have hmem : orderOf (3 : ZMod 41) ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  generalize ho : orderOf (3 : ZMod 41) = o at hdvd hn4 hn2 n4 n2 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨4, by norm_num⟩ : (1 : Nat) ∣ 4) n4
  · exact absurd (⟨2, by norm_num⟩ : (2 : Nat) ∣ 4) n4
  · exact absurd (⟨1, by norm_num⟩ : (4 : Nat) ∣ 4) n4
  · rfl
