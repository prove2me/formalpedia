-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_443_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:54:30.301837+00:00
-- url     : https://prove2.me/submissions/830a5335-86bc-4b75-9744-22bcb5acc733

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (443 : ZMod 449)) ∧ orderOf (443 : ZMod 449) = 448 := by
  have hN : (443 : ZMod 449) ^ 448 = 1 := by decide
  have h224 : (443 : ZMod 449) ^ 224 ≠ 1 := by decide
  have h64 : (443 : ZMod 449) ^ 64 ≠ 1 := by decide
  have hdvd : orderOf (443 : ZMod 449) ∣ 448 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (443 : ZMod 449) ∣ k →
      (443 : ZMod 449) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (443 : ZMod 449)
    have hcon : (443 : ZMod 449) ^ (orderOf (443 : ZMod 449) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n224 : ¬ orderOf (443 : ZMod 449) ∣ 224 := fun h => mk 224 h h224
  have n64 : ¬ orderOf (443 : ZMod 449) ∣ 64 := fun h => mk 64 h h64
  have hmem : orderOf (443 : ZMod 449) ∈ Nat.divisors 448 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 448 = {1, 2, 4, 7, 8, 14, 16, 28, 32, 56, 64, 112, 224, 448} := by decide
  generalize ho : orderOf (443 : ZMod 449) = v at hdvd n224 n64 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 448 := by
    fin_cases hmem
    · exact absurd (⟨224, by norm_num⟩ : (1 : Nat) ∣ 224) n224
    · exact absurd (⟨112, by norm_num⟩ : (2 : Nat) ∣ 224) n224
    · exact absurd (⟨56, by norm_num⟩ : (4 : Nat) ∣ 224) n224
    · exact absurd (⟨32, by norm_num⟩ : (7 : Nat) ∣ 224) n224
    · exact absurd (⟨28, by norm_num⟩ : (8 : Nat) ∣ 224) n224
    · exact absurd (⟨16, by norm_num⟩ : (14 : Nat) ∣ 224) n224
    · exact absurd (⟨14, by norm_num⟩ : (16 : Nat) ∣ 224) n224
    · exact absurd (⟨8, by norm_num⟩ : (28 : Nat) ∣ 224) n224
    · exact absurd (⟨7, by norm_num⟩ : (32 : Nat) ∣ 224) n224
    · exact absurd (⟨4, by norm_num⟩ : (56 : Nat) ∣ 224) n224
    · exact absurd (⟨1, by norm_num⟩ : (64 : Nat) ∣ 64) n64
    · exact absurd (⟨2, by norm_num⟩ : (112 : Nat) ∣ 224) n224
    · exact absurd (⟨1, by norm_num⟩ : (224 : Nat) ∣ 224) n224
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
