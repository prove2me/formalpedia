-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_order37_3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T12:35:57.120735+00:00
-- url     : https://prove2.me/submissions/d858cfbb-bd7d-4bcb-8f5c-40b22ea1cde4

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 37) = 18 := by
  have hN : (3 : ZMod 37) ^ 18 = 1 := by decide
  have hn9 : (3 : ZMod 37) ^ 9 ≠ 1 := by decide
  have hn6 : (3 : ZMod 37) ^ 6 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 37) ∣ 18 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 37) ∣ k → (3 : ZMod 37) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 37)
    have hcon : (3 : ZMod 37) ^ (orderOf (3 : ZMod 37) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n9 : ¬ orderOf (3 : ZMod 37) ∣ 9 := fun h => mk 9 h hn9
  have n6 : ¬ orderOf (3 : ZMod 37) ∣ 6 := fun h => mk 6 h hn6
  have hmem : orderOf (3 : ZMod 37) ∈ Nat.divisors 18 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 18 = {1, 2, 3, 6, 9, 18} := by decide
  generalize ho : orderOf (3 : ZMod 37) = o at hdvd hn9 hn6 n9 n6 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨9, by norm_num⟩ : (1 : Nat) ∣ 9) n9
  · exact absurd (⟨3, by norm_num⟩ : (2 : Nat) ∣ 6) n6
  · exact absurd (⟨3, by norm_num⟩ : (3 : Nat) ∣ 9) n9
  · exact absurd (⟨1, by norm_num⟩ : (6 : Nat) ∣ 6) n6
  · exact absurd (⟨1, by norm_num⟩ : (9 : Nat) ∣ 9) n9
  · rfl
