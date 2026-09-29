-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_order3571_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:11:49.161272+00:00
-- url     : https://prove2.me/submissions/92e14c70-7320-47a4-97e0-3fd1af2c415f

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 3571) = 3570 := by
  have hN : (3 : ZMod 3571) ^ 3570 = 1 := by decide
  have h1785 : (3 : ZMod 3571) ^ 1785 ≠ 1 := by decide
  have h1190 : (3 : ZMod 3571) ^ 1190 ≠ 1 := by decide
  have h714 : (3 : ZMod 3571) ^ 714 ≠ 1 := by decide
  have h510 : (3 : ZMod 3571) ^ 510 ≠ 1 := by decide
  have h210 : (3 : ZMod 3571) ^ 210 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 3571) ∣ 3570 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 3571) ∣ k →
      (3 : ZMod 3571) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 3571)
    have hcon : (3 : ZMod 3571) ^ (orderOf (3 : ZMod 3571) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n1785 : ¬ orderOf (3 : ZMod 3571) ∣ 1785 := fun h => mk 1785 h h1785
  have n1190 : ¬ orderOf (3 : ZMod 3571) ∣ 1190 := fun h => mk 1190 h h1190
  have n714 : ¬ orderOf (3 : ZMod 3571) ∣ 714 := fun h => mk 714 h h714
  have n510 : ¬ orderOf (3 : ZMod 3571) ∣ 510 := fun h => mk 510 h h510
  have n210 : ¬ orderOf (3 : ZMod 3571) ∣ 210 := fun h => mk 210 h h210
  have hmem : orderOf (3 : ZMod 3571) ∈ Nat.divisors 3570 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 3570 = {1, 2, 3, 5, 6, 7, 10, 14, 15, 17, 21, 30, 34, 35, 42, 51, 70, 85, 102, 105, 119, 170, 210, 238, 255, 357, 510, 595, 714, 1190, 1785, 3570} := by decide
  generalize ho : orderOf (3 : ZMod 3571) = o at hdvd n1785 n1190 n714 n510 n210 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨1785, by norm_num⟩ : (1 : Nat) ∣ 1785) n1785
  · exact absurd (⟨595, by norm_num⟩ : (2 : Nat) ∣ 1190) n1190
  · exact absurd (⟨595, by norm_num⟩ : (3 : Nat) ∣ 1785) n1785
  · exact absurd (⟨357, by norm_num⟩ : (5 : Nat) ∣ 1785) n1785
  · exact absurd (⟨119, by norm_num⟩ : (6 : Nat) ∣ 714) n714
  · exact absurd (⟨255, by norm_num⟩ : (7 : Nat) ∣ 1785) n1785
  · exact absurd (⟨119, by norm_num⟩ : (10 : Nat) ∣ 1190) n1190
  · exact absurd (⟨85, by norm_num⟩ : (14 : Nat) ∣ 1190) n1190
  · exact absurd (⟨119, by norm_num⟩ : (15 : Nat) ∣ 1785) n1785
  · exact absurd (⟨105, by norm_num⟩ : (17 : Nat) ∣ 1785) n1785
  · exact absurd (⟨85, by norm_num⟩ : (21 : Nat) ∣ 1785) n1785
  · exact absurd (⟨17, by norm_num⟩ : (30 : Nat) ∣ 510) n510
  · exact absurd (⟨35, by norm_num⟩ : (34 : Nat) ∣ 1190) n1190
  · exact absurd (⟨51, by norm_num⟩ : (35 : Nat) ∣ 1785) n1785
  · exact absurd (⟨17, by norm_num⟩ : (42 : Nat) ∣ 714) n714
  · exact absurd (⟨35, by norm_num⟩ : (51 : Nat) ∣ 1785) n1785
  · exact absurd (⟨17, by norm_num⟩ : (70 : Nat) ∣ 1190) n1190
  · exact absurd (⟨21, by norm_num⟩ : (85 : Nat) ∣ 1785) n1785
  · exact absurd (⟨7, by norm_num⟩ : (102 : Nat) ∣ 714) n714
  · exact absurd (⟨17, by norm_num⟩ : (105 : Nat) ∣ 1785) n1785
  · exact absurd (⟨15, by norm_num⟩ : (119 : Nat) ∣ 1785) n1785
  · exact absurd (⟨7, by norm_num⟩ : (170 : Nat) ∣ 1190) n1190
  · exact absurd (⟨1, by norm_num⟩ : (210 : Nat) ∣ 210) n210
  · exact absurd (⟨5, by norm_num⟩ : (238 : Nat) ∣ 1190) n1190
  · exact absurd (⟨7, by norm_num⟩ : (255 : Nat) ∣ 1785) n1785
  · exact absurd (⟨5, by norm_num⟩ : (357 : Nat) ∣ 1785) n1785
  · exact absurd (⟨1, by norm_num⟩ : (510 : Nat) ∣ 510) n510
  · exact absurd (⟨3, by norm_num⟩ : (595 : Nat) ∣ 1785) n1785
  · exact absurd (⟨1, by norm_num⟩ : (714 : Nat) ∣ 714) n714
  · exact absurd (⟨1, by norm_num⟩ : (1190 : Nat) ∣ 1190) n1190
  · exact absurd (⟨1, by norm_num⟩ : (1785 : Nat) ∣ 1785) n1785
  · rfl
