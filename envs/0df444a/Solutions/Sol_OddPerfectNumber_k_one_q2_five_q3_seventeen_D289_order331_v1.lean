-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order331_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:00:16.88601+00:00
-- url     : https://prove2.me/submissions/8b906cae-8b49-4c64-86fc-02d8db6e4b9b

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 331) = 330 := by
  have h330 : (3 : ZMod 331) ^ 330 = 1 := by decide
  have h165 : (3 : ZMod 331) ^ 165 ≠ 1 := by decide
  have h110 : (3 : ZMod 331) ^ 110 ≠ 1 := by decide
  have h66 : (3 : ZMod 331) ^ 66 ≠ 1 := by decide
  have h30 : (3 : ZMod 331) ^ 30 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 331) ∣ 330 := orderOf_dvd_of_pow_eq_one h330
  have mk : ∀ k : Nat, orderOf (3 : ZMod 331) ∣ k →
      (3 : ZMod 331) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 331)
    have hcon : (3 : ZMod 331) ^ (orderOf (3 : ZMod 331) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n165 : ¬ orderOf (3 : ZMod 331) ∣ 165 := fun h => mk 165 h h165
  have n110 : ¬ orderOf (3 : ZMod 331) ∣ 110 := fun h => mk 110 h h110
  have n66 : ¬ orderOf (3 : ZMod 331) ∣ 66 := fun h => mk 66 h h66
  have n30 : ¬ orderOf (3 : ZMod 331) ∣ 30 := fun h => mk 30 h h30
  have hmem : orderOf (3 : ZMod 331) ∈ Nat.divisors 330 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 330 = {1, 2, 3, 5, 6, 10, 11, 15, 22, 30, 33, 55, 66, 110, 165, 330} := by decide
  generalize ho : orderOf (3 : ZMod 331) = o at hdvd n165 n110 n66 n30 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨165, by norm_num⟩ : (1 : Nat) ∣ 165) n165
  · exact absurd (⟨55, by norm_num⟩ : (2 : Nat) ∣ 110) n110
  · exact absurd (⟨55, by norm_num⟩ : (3 : Nat) ∣ 165) n165
  · exact absurd (⟨33, by norm_num⟩ : (5 : Nat) ∣ 165) n165
  · exact absurd (⟨11, by norm_num⟩ : (6 : Nat) ∣ 66) n66
  · exact absurd (⟨11, by norm_num⟩ : (10 : Nat) ∣ 110) n110
  · exact absurd (⟨15, by norm_num⟩ : (11 : Nat) ∣ 165) n165
  · exact absurd (⟨11, by norm_num⟩ : (15 : Nat) ∣ 165) n165
  · exact absurd (⟨5, by norm_num⟩ : (22 : Nat) ∣ 110) n110
  · exact absurd (⟨1, by norm_num⟩ : (30 : Nat) ∣ 30) n30
  · exact absurd (⟨5, by norm_num⟩ : (33 : Nat) ∣ 165) n165
  · exact absurd (⟨3, by norm_num⟩ : (55 : Nat) ∣ 165) n165
  · exact absurd (⟨1, by norm_num⟩ : (66 : Nat) ∣ 66) n66
  · exact absurd (⟨1, by norm_num⟩ : (110 : Nat) ∣ 110) n110
  · exact absurd (⟨1, by norm_num⟩ : (165 : Nat) ∣ 165) n165
  · rfl
