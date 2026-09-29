-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:54:38.016561+00:00
-- url     : https://prove2.me/submissions/3e71d5b2-45ac-4823-983b-693fd2dce54c

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (3 : ZMod 577)) ∧ orderOf (3 : ZMod 577) = 48 := by
  have hN : (3 : ZMod 577) ^ 48 = 1 := by decide
  have h24 : (3 : ZMod 577) ^ 24 ≠ 1 := by decide
  have h16 : (3 : ZMod 577) ^ 16 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 577) ∣ 48 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 577) ∣ k →
      (3 : ZMod 577) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 577)
    have hcon : (3 : ZMod 577) ^ (orderOf (3 : ZMod 577) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n24 : ¬ orderOf (3 : ZMod 577) ∣ 24 := fun h => mk 24 h h24
  have n16 : ¬ orderOf (3 : ZMod 577) ∣ 16 := fun h => mk 16 h h16
  have hmem : orderOf (3 : ZMod 577) ∈ Nat.divisors 48 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 48 = {1, 2, 3, 4, 6, 8, 12, 16, 24, 48} := by decide
  generalize ho : orderOf (3 : ZMod 577) = v at hdvd n24 n16 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 48 := by
    fin_cases hmem
    · exact absurd (⟨24, by norm_num⟩ : (1 : Nat) ∣ 24) n24
    · exact absurd (⟨12, by norm_num⟩ : (2 : Nat) ∣ 24) n24
    · exact absurd (⟨8, by norm_num⟩ : (3 : Nat) ∣ 24) n24
    · exact absurd (⟨6, by norm_num⟩ : (4 : Nat) ∣ 24) n24
    · exact absurd (⟨4, by norm_num⟩ : (6 : Nat) ∣ 24) n24
    · exact absurd (⟨3, by norm_num⟩ : (8 : Nat) ∣ 24) n24
    · exact absurd (⟨2, by norm_num⟩ : (12 : Nat) ∣ 24) n24
    · exact absurd (⟨1, by norm_num⟩ : (16 : Nat) ∣ 16) n16
    · exact absurd (⟨1, by norm_num⟩ : (24 : Nat) ∣ 24) n24
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
