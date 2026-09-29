-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_order3061_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:06:17.867313+00:00
-- url     : https://prove2.me/submissions/41149ee7-9860-48f6-9f8e-1fc9f68adc25

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 3061) = 1530 := by
  have h1530 : (3 : ZMod 3061) ^ 1530 = 1 := by decide
  have h765 : (3 : ZMod 3061) ^ 765 ≠ 1 := by decide
  have h510 : (3 : ZMod 3061) ^ 510 ≠ 1 := by decide
  have h306 : (3 : ZMod 3061) ^ 306 ≠ 1 := by decide
  have h90 : (3 : ZMod 3061) ^ 90 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 3061) ∣ 1530 := orderOf_dvd_of_pow_eq_one h1530
  have mk : ∀ k : Nat, orderOf (3 : ZMod 3061) ∣ k →
      (3 : ZMod 3061) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 3061)
    have hcon : (3 : ZMod 3061) ^ (orderOf (3 : ZMod 3061) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n765 : ¬ orderOf (3 : ZMod 3061) ∣ 765 := fun h => mk 765 h h765
  have n510 : ¬ orderOf (3 : ZMod 3061) ∣ 510 := fun h => mk 510 h h510
  have n306 : ¬ orderOf (3 : ZMod 3061) ∣ 306 := fun h => mk 306 h h306
  have n90 : ¬ orderOf (3 : ZMod 3061) ∣ 90 := fun h => mk 90 h h90
  have hmem : orderOf (3 : ZMod 3061) ∈ Nat.divisors 1530 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 1530 = {1, 2, 3, 5, 6, 9, 10, 15, 17, 18, 30, 34, 45, 51, 85, 90, 102, 153, 170, 255, 306, 510, 765, 1530} := by decide
  generalize ho : orderOf (3 : ZMod 3061) = o at hdvd n765 n510 n306 n90 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨765, by norm_num⟩ : (1 : Nat) ∣ 765) n765
  · exact absurd (⟨255, by norm_num⟩ : (2 : Nat) ∣ 510) n510
  · exact absurd (⟨255, by norm_num⟩ : (3 : Nat) ∣ 765) n765
  · exact absurd (⟨153, by norm_num⟩ : (5 : Nat) ∣ 765) n765
  · exact absurd (⟨85, by norm_num⟩ : (6 : Nat) ∣ 510) n510
  · exact absurd (⟨85, by norm_num⟩ : (9 : Nat) ∣ 765) n765
  · exact absurd (⟨51, by norm_num⟩ : (10 : Nat) ∣ 510) n510
  · exact absurd (⟨51, by norm_num⟩ : (15 : Nat) ∣ 765) n765
  · exact absurd (⟨45, by norm_num⟩ : (17 : Nat) ∣ 765) n765
  · exact absurd (⟨17, by norm_num⟩ : (18 : Nat) ∣ 306) n306
  · exact absurd (⟨17, by norm_num⟩ : (30 : Nat) ∣ 510) n510
  · exact absurd (⟨15, by norm_num⟩ : (34 : Nat) ∣ 510) n510
  · exact absurd (⟨17, by norm_num⟩ : (45 : Nat) ∣ 765) n765
  · exact absurd (⟨15, by norm_num⟩ : (51 : Nat) ∣ 765) n765
  · exact absurd (⟨9, by norm_num⟩ : (85 : Nat) ∣ 765) n765
  · exact absurd (⟨1, by norm_num⟩ : (90 : Nat) ∣ 90) n90
  · exact absurd (⟨5, by norm_num⟩ : (102 : Nat) ∣ 510) n510
  · exact absurd (⟨5, by norm_num⟩ : (153 : Nat) ∣ 765) n765
  · exact absurd (⟨3, by norm_num⟩ : (170 : Nat) ∣ 510) n510
  · exact absurd (⟨3, by norm_num⟩ : (255 : Nat) ∣ 765) n765
  · exact absurd (⟨1, by norm_num⟩ : (306 : Nat) ∣ 306) n306
  · exact absurd (⟨1, by norm_num⟩ : (510 : Nat) ∣ 510) n510
  · exact absurd (⟨1, by norm_num⟩ : (765 : Nat) ∣ 765) n765
  · rfl
