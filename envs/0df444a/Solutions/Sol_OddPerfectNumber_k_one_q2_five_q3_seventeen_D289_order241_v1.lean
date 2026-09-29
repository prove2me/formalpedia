-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order241_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:56:44.665762+00:00
-- url     : https://prove2.me/submissions/bf8b096a-2787-4683-aceb-042939600806

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 241) = 120 := by
  have h120 : (3 : ZMod 241) ^ 120 = 1 := by decide
  have h60 : (3 : ZMod 241) ^ 60 ≠ 1 := by decide
  have h40 : (3 : ZMod 241) ^ 40 ≠ 1 := by decide
  have h24 : (3 : ZMod 241) ^ 24 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 241) ∣ 120 := orderOf_dvd_of_pow_eq_one h120
  have mk : ∀ k : Nat, orderOf (3 : ZMod 241) ∣ k →
      (3 : ZMod 241) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 241)
    have hcon : (3 : ZMod 241) ^ (orderOf (3 : ZMod 241) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n60 : ¬ orderOf (3 : ZMod 241) ∣ 60 := fun h => mk 60 h h60
  have n40 : ¬ orderOf (3 : ZMod 241) ∣ 40 := fun h => mk 40 h h40
  have n24 : ¬ orderOf (3 : ZMod 241) ∣ 24 := fun h => mk 24 h h24
  have hmem : orderOf (3 : ZMod 241) ∈ Nat.divisors 120 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 120 = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} := by decide
  generalize ho : orderOf (3 : ZMod 241) = o at hdvd n60 n40 n24 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨60, by norm_num⟩ : (1 : Nat) ∣ 60) n60
  · exact absurd (⟨30, by norm_num⟩ : (2 : Nat) ∣ 60) n60
  · exact absurd (⟨20, by norm_num⟩ : (3 : Nat) ∣ 60) n60
  · exact absurd (⟨15, by norm_num⟩ : (4 : Nat) ∣ 60) n60
  · exact absurd (⟨12, by norm_num⟩ : (5 : Nat) ∣ 60) n60
  · exact absurd (⟨10, by norm_num⟩ : (6 : Nat) ∣ 60) n60
  · exact absurd (⟨5, by norm_num⟩ : (8 : Nat) ∣ 40) n40
  · exact absurd (⟨6, by norm_num⟩ : (10 : Nat) ∣ 60) n60
  · exact absurd (⟨5, by norm_num⟩ : (12 : Nat) ∣ 60) n60
  · exact absurd (⟨4, by norm_num⟩ : (15 : Nat) ∣ 60) n60
  · exact absurd (⟨3, by norm_num⟩ : (20 : Nat) ∣ 60) n60
  · exact absurd (⟨1, by norm_num⟩ : (24 : Nat) ∣ 24) n24
  · exact absurd (⟨2, by norm_num⟩ : (30 : Nat) ∣ 60) n60
  · exact absurd (⟨1, by norm_num⟩ : (40 : Nat) ∣ 40) n40
  · exact absurd (⟨1, by norm_num⟩ : (60 : Nat) ∣ 60) n60
  · rfl
