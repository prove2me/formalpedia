-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_409_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:54:26.330531+00:00
-- url     : https://prove2.me/submissions/81d81e82-dc75-48e5-9f86-82c9b222b594

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (409 : ZMod 449)) ∧ orderOf (409 : ZMod 449) = 224 := by
  have hN : (409 : ZMod 449) ^ 224 = 1 := by decide
  have h112 : (409 : ZMod 449) ^ 112 ≠ 1 := by decide
  have h32 : (409 : ZMod 449) ^ 32 ≠ 1 := by decide
  have hdvd : orderOf (409 : ZMod 449) ∣ 224 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (409 : ZMod 449) ∣ k →
      (409 : ZMod 449) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (409 : ZMod 449)
    have hcon : (409 : ZMod 449) ^ (orderOf (409 : ZMod 449) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n112 : ¬ orderOf (409 : ZMod 449) ∣ 112 := fun h => mk 112 h h112
  have n32 : ¬ orderOf (409 : ZMod 449) ∣ 32 := fun h => mk 32 h h32
  have hmem : orderOf (409 : ZMod 449) ∈ Nat.divisors 224 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 224 = {1, 2, 4, 7, 8, 14, 16, 28, 32, 56, 112, 224} := by decide
  generalize ho : orderOf (409 : ZMod 449) = v at hdvd n112 n32 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 224 := by
    fin_cases hmem
    · exact absurd (⟨112, by norm_num⟩ : (1 : Nat) ∣ 112) n112
    · exact absurd (⟨56, by norm_num⟩ : (2 : Nat) ∣ 112) n112
    · exact absurd (⟨28, by norm_num⟩ : (4 : Nat) ∣ 112) n112
    · exact absurd (⟨16, by norm_num⟩ : (7 : Nat) ∣ 112) n112
    · exact absurd (⟨14, by norm_num⟩ : (8 : Nat) ∣ 112) n112
    · exact absurd (⟨8, by norm_num⟩ : (14 : Nat) ∣ 112) n112
    · exact absurd (⟨7, by norm_num⟩ : (16 : Nat) ∣ 112) n112
    · exact absurd (⟨4, by norm_num⟩ : (28 : Nat) ∣ 112) n112
    · exact absurd (⟨1, by norm_num⟩ : (32 : Nat) ∣ 32) n32
    · exact absurd (⟨2, by norm_num⟩ : (56 : Nat) ∣ 112) n112
    · exact absurd (⟨1, by norm_num⟩ : (112 : Nat) ∣ 112) n112
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
