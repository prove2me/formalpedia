-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order211_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:56:40.446979+00:00
-- url     : https://prove2.me/submissions/ac43f763-994b-4b01-b905-2c490f3f8eb3

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 211) = 210 := by
  have h210 : (3 : ZMod 211) ^ 210 = 1 := by decide
  have h105 : (3 : ZMod 211) ^ 105 ≠ 1 := by decide
  have h70 : (3 : ZMod 211) ^ 70 ≠ 1 := by decide
  have h42 : (3 : ZMod 211) ^ 42 ≠ 1 := by decide
  have h30 : (3 : ZMod 211) ^ 30 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 211) ∣ 210 := orderOf_dvd_of_pow_eq_one h210
  have mk : ∀ k : Nat, orderOf (3 : ZMod 211) ∣ k →
      (3 : ZMod 211) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 211)
    have hcon : (3 : ZMod 211) ^ (orderOf (3 : ZMod 211) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n105 : ¬ orderOf (3 : ZMod 211) ∣ 105 := fun h => mk 105 h h105
  have n70 : ¬ orderOf (3 : ZMod 211) ∣ 70 := fun h => mk 70 h h70
  have n42 : ¬ orderOf (3 : ZMod 211) ∣ 42 := fun h => mk 42 h h42
  have n30 : ¬ orderOf (3 : ZMod 211) ∣ 30 := fun h => mk 30 h h30
  have hmem : orderOf (3 : ZMod 211) ∈ Nat.divisors 210 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 210 = {1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210} := by decide
  generalize ho : orderOf (3 : ZMod 211) = o at hdvd n105 n70 n42 n30 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨105, by norm_num⟩ : (1 : Nat) ∣ 105) n105
  · exact absurd (⟨35, by norm_num⟩ : (2 : Nat) ∣ 70) n70
  · exact absurd (⟨35, by norm_num⟩ : (3 : Nat) ∣ 105) n105
  · exact absurd (⟨21, by norm_num⟩ : (5 : Nat) ∣ 105) n105
  · exact absurd (⟨7, by norm_num⟩ : (6 : Nat) ∣ 42) n42
  · exact absurd (⟨15, by norm_num⟩ : (7 : Nat) ∣ 105) n105
  · exact absurd (⟨7, by norm_num⟩ : (10 : Nat) ∣ 70) n70
  · exact absurd (⟨5, by norm_num⟩ : (14 : Nat) ∣ 70) n70
  · exact absurd (⟨7, by norm_num⟩ : (15 : Nat) ∣ 105) n105
  · exact absurd (⟨5, by norm_num⟩ : (21 : Nat) ∣ 105) n105
  · exact absurd (⟨1, by norm_num⟩ : (30 : Nat) ∣ 30) n30
  · exact absurd (⟨3, by norm_num⟩ : (35 : Nat) ∣ 105) n105
  · exact absurd (⟨1, by norm_num⟩ : (42 : Nat) ∣ 42) n42
  · exact absurd (⟨1, by norm_num⟩ : (70 : Nat) ∣ 70) n70
  · exact absurd (⟨1, by norm_num⟩ : (105 : Nat) ∣ 105) n105
  · rfl
