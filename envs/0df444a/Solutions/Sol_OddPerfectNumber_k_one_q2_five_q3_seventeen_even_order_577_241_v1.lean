-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_241_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:55:07.38795+00:00
-- url     : https://prove2.me/submissions/ecb5d92c-02e0-482b-acfe-8339a29d9497

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (241 : ZMod 577)) ∧ orderOf (241 : ZMod 577) = 192 := by
  have hN : (241 : ZMod 577) ^ 192 = 1 := by decide
  have h96 : (241 : ZMod 577) ^ 96 ≠ 1 := by decide
  have h64 : (241 : ZMod 577) ^ 64 ≠ 1 := by decide
  have hdvd : orderOf (241 : ZMod 577) ∣ 192 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (241 : ZMod 577) ∣ k →
      (241 : ZMod 577) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (241 : ZMod 577)
    have hcon : (241 : ZMod 577) ^ (orderOf (241 : ZMod 577) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n96 : ¬ orderOf (241 : ZMod 577) ∣ 96 := fun h => mk 96 h h96
  have n64 : ¬ orderOf (241 : ZMod 577) ∣ 64 := fun h => mk 64 h h64
  have hmem : orderOf (241 : ZMod 577) ∈ Nat.divisors 192 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 192 = {1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 192} := by decide
  generalize ho : orderOf (241 : ZMod 577) = v at hdvd n96 n64 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 192 := by
    fin_cases hmem
    · exact absurd (⟨96, by norm_num⟩ : (1 : Nat) ∣ 96) n96
    · exact absurd (⟨48, by norm_num⟩ : (2 : Nat) ∣ 96) n96
    · exact absurd (⟨32, by norm_num⟩ : (3 : Nat) ∣ 96) n96
    · exact absurd (⟨24, by norm_num⟩ : (4 : Nat) ∣ 96) n96
    · exact absurd (⟨16, by norm_num⟩ : (6 : Nat) ∣ 96) n96
    · exact absurd (⟨12, by norm_num⟩ : (8 : Nat) ∣ 96) n96
    · exact absurd (⟨8, by norm_num⟩ : (12 : Nat) ∣ 96) n96
    · exact absurd (⟨6, by norm_num⟩ : (16 : Nat) ∣ 96) n96
    · exact absurd (⟨4, by norm_num⟩ : (24 : Nat) ∣ 96) n96
    · exact absurd (⟨3, by norm_num⟩ : (32 : Nat) ∣ 96) n96
    · exact absurd (⟨2, by norm_num⟩ : (48 : Nat) ∣ 96) n96
    · exact absurd (⟨1, by norm_num⟩ : (64 : Nat) ∣ 64) n64
    · exact absurd (⟨1, by norm_num⟩ : (96 : Nat) ∣ 96) n96
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
