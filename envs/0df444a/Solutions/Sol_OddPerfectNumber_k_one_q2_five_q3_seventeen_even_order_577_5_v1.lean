-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_5_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:54:41.924929+00:00
-- url     : https://prove2.me/submissions/d33d1076-1180-43e7-97f7-9f218481b948

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (5 : ZMod 577)) ∧ orderOf (5 : ZMod 577) = 576 := by
  have hN : (5 : ZMod 577) ^ 576 = 1 := by decide
  have h288 : (5 : ZMod 577) ^ 288 ≠ 1 := by decide
  have h192 : (5 : ZMod 577) ^ 192 ≠ 1 := by decide
  have hdvd : orderOf (5 : ZMod 577) ∣ 576 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (5 : ZMod 577) ∣ k →
      (5 : ZMod 577) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (5 : ZMod 577)
    have hcon : (5 : ZMod 577) ^ (orderOf (5 : ZMod 577) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n288 : ¬ orderOf (5 : ZMod 577) ∣ 288 := fun h => mk 288 h h288
  have n192 : ¬ orderOf (5 : ZMod 577) ∣ 192 := fun h => mk 192 h h192
  have hmem : orderOf (5 : ZMod 577) ∈ Nat.divisors 576 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 576 = {1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 36, 48, 64, 72, 96, 144, 192, 288, 576} := by decide
  generalize ho : orderOf (5 : ZMod 577) = v at hdvd n288 n192 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 576 := by
    fin_cases hmem
    · exact absurd (⟨288, by norm_num⟩ : (1 : Nat) ∣ 288) n288
    · exact absurd (⟨144, by norm_num⟩ : (2 : Nat) ∣ 288) n288
    · exact absurd (⟨96, by norm_num⟩ : (3 : Nat) ∣ 288) n288
    · exact absurd (⟨72, by norm_num⟩ : (4 : Nat) ∣ 288) n288
    · exact absurd (⟨48, by norm_num⟩ : (6 : Nat) ∣ 288) n288
    · exact absurd (⟨36, by norm_num⟩ : (8 : Nat) ∣ 288) n288
    · exact absurd (⟨32, by norm_num⟩ : (9 : Nat) ∣ 288) n288
    · exact absurd (⟨24, by norm_num⟩ : (12 : Nat) ∣ 288) n288
    · exact absurd (⟨18, by norm_num⟩ : (16 : Nat) ∣ 288) n288
    · exact absurd (⟨16, by norm_num⟩ : (18 : Nat) ∣ 288) n288
    · exact absurd (⟨12, by norm_num⟩ : (24 : Nat) ∣ 288) n288
    · exact absurd (⟨9, by norm_num⟩ : (32 : Nat) ∣ 288) n288
    · exact absurd (⟨8, by norm_num⟩ : (36 : Nat) ∣ 288) n288
    · exact absurd (⟨6, by norm_num⟩ : (48 : Nat) ∣ 288) n288
    · exact absurd (⟨3, by norm_num⟩ : (64 : Nat) ∣ 192) n192
    · exact absurd (⟨4, by norm_num⟩ : (72 : Nat) ∣ 288) n288
    · exact absurd (⟨3, by norm_num⟩ : (96 : Nat) ∣ 288) n288
    · exact absurd (⟨2, by norm_num⟩ : (144 : Nat) ∣ 288) n288
    · exact absurd (⟨1, by norm_num⟩ : (192 : Nat) ∣ 192) n192
    · exact absurd (⟨1, by norm_num⟩ : (288 : Nat) ∣ 288) n288
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
