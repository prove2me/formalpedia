-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_order2551_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:03:57.925426+00:00
-- url     : https://prove2.me/submissions/a62961d7-e5b2-405f-9e88-50cac403955b

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 2551) = 150 := by
  have h150 : (3 : ZMod 2551) ^ 150 = 1 := by decide
  have h75 : (3 : ZMod 2551) ^ 75 ≠ 1 := by decide
  have h50 : (3 : ZMod 2551) ^ 50 ≠ 1 := by decide
  have h30 : (3 : ZMod 2551) ^ 30 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 2551) ∣ 150 := orderOf_dvd_of_pow_eq_one h150
  have mk : ∀ k : Nat, orderOf (3 : ZMod 2551) ∣ k →
      (3 : ZMod 2551) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 2551)
    have hcon : (3 : ZMod 2551) ^ (orderOf (3 : ZMod 2551) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n75 : ¬ orderOf (3 : ZMod 2551) ∣ 75 := fun h => mk 75 h h75
  have n50 : ¬ orderOf (3 : ZMod 2551) ∣ 50 := fun h => mk 50 h h50
  have n30 : ¬ orderOf (3 : ZMod 2551) ∣ 30 := fun h => mk 30 h h30
  have hmem : orderOf (3 : ZMod 2551) ∈ Nat.divisors 150 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 150 = {1, 2, 3, 5, 6, 10, 15, 25, 30, 50, 75, 150} := by decide
  generalize ho : orderOf (3 : ZMod 2551) = o at hdvd n75 n50 n30 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨75, by norm_num⟩ : (1 : Nat) ∣ 75) n75
  · exact absurd (⟨25, by norm_num⟩ : (2 : Nat) ∣ 50) n50
  · exact absurd (⟨25, by norm_num⟩ : (3 : Nat) ∣ 75) n75
  · exact absurd (⟨15, by norm_num⟩ : (5 : Nat) ∣ 75) n75
  · exact absurd (⟨5, by norm_num⟩ : (6 : Nat) ∣ 30) n30
  · exact absurd (⟨5, by norm_num⟩ : (10 : Nat) ∣ 50) n50
  · exact absurd (⟨5, by norm_num⟩ : (15 : Nat) ∣ 75) n75
  · exact absurd (⟨3, by norm_num⟩ : (25 : Nat) ∣ 75) n75
  · exact absurd (⟨1, by norm_num⟩ : (30 : Nat) ∣ 30) n30
  · exact absurd (⟨1, by norm_num⟩ : (50 : Nat) ∣ 50) n50
  · exact absurd (⟨1, by norm_num⟩ : (75 : Nat) ∣ 75) n75
  · rfl
