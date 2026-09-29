-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_271_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:55:11.641149+00:00
-- url     : https://prove2.me/submissions/23f8876a-599f-4ed6-908b-838c9af14d94

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (271 : ZMod 577)) ∧ orderOf (271 : ZMod 577) = 288 := by
  have hN : (271 : ZMod 577) ^ 288 = 1 := by decide
  have h144 : (271 : ZMod 577) ^ 144 ≠ 1 := by decide
  have h96 : (271 : ZMod 577) ^ 96 ≠ 1 := by decide
  have hdvd : orderOf (271 : ZMod 577) ∣ 288 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (271 : ZMod 577) ∣ k →
      (271 : ZMod 577) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (271 : ZMod 577)
    have hcon : (271 : ZMod 577) ^ (orderOf (271 : ZMod 577) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n144 : ¬ orderOf (271 : ZMod 577) ∣ 144 := fun h => mk 144 h h144
  have n96 : ¬ orderOf (271 : ZMod 577) ∣ 96 := fun h => mk 96 h h96
  have hmem : orderOf (271 : ZMod 577) ∈ Nat.divisors 288 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 288 = {1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 36, 48, 72, 96, 144, 288} := by decide
  generalize ho : orderOf (271 : ZMod 577) = v at hdvd n144 n96 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 288 := by
    fin_cases hmem
    · exact absurd (⟨144, by norm_num⟩ : (1 : Nat) ∣ 144) n144
    · exact absurd (⟨72, by norm_num⟩ : (2 : Nat) ∣ 144) n144
    · exact absurd (⟨48, by norm_num⟩ : (3 : Nat) ∣ 144) n144
    · exact absurd (⟨36, by norm_num⟩ : (4 : Nat) ∣ 144) n144
    · exact absurd (⟨24, by norm_num⟩ : (6 : Nat) ∣ 144) n144
    · exact absurd (⟨18, by norm_num⟩ : (8 : Nat) ∣ 144) n144
    · exact absurd (⟨16, by norm_num⟩ : (9 : Nat) ∣ 144) n144
    · exact absurd (⟨12, by norm_num⟩ : (12 : Nat) ∣ 144) n144
    · exact absurd (⟨9, by norm_num⟩ : (16 : Nat) ∣ 144) n144
    · exact absurd (⟨8, by norm_num⟩ : (18 : Nat) ∣ 144) n144
    · exact absurd (⟨6, by norm_num⟩ : (24 : Nat) ∣ 144) n144
    · exact absurd (⟨3, by norm_num⟩ : (32 : Nat) ∣ 96) n96
    · exact absurd (⟨4, by norm_num⟩ : (36 : Nat) ∣ 144) n144
    · exact absurd (⟨3, by norm_num⟩ : (48 : Nat) ∣ 144) n144
    · exact absurd (⟨2, by norm_num⟩ : (72 : Nat) ∣ 144) n144
    · exact absurd (⟨1, by norm_num⟩ : (96 : Nat) ∣ 96) n96
    · exact absurd (⟨1, by norm_num⟩ : (144 : Nat) ∣ 144) n144
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
