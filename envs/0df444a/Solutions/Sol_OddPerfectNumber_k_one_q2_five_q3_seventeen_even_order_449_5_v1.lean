-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_449_5_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:53:59.002211+00:00
-- url     : https://prove2.me/submissions/dfbf1332-7ca2-4535-88e8-2657a227cd51

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (5 : ZMod 449)) ∧ orderOf (5 : ZMod 449) = 14 := by
  have hN : (5 : ZMod 449) ^ 14 = 1 := by decide
  have h7 : (5 : ZMod 449) ^ 7 ≠ 1 := by decide
  have h2 : (5 : ZMod 449) ^ 2 ≠ 1 := by decide
  have hdvd : orderOf (5 : ZMod 449) ∣ 14 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (5 : ZMod 449) ∣ k →
      (5 : ZMod 449) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (5 : ZMod 449)
    have hcon : (5 : ZMod 449) ^ (orderOf (5 : ZMod 449) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n7 : ¬ orderOf (5 : ZMod 449) ∣ 7 := fun h => mk 7 h h7
  have n2 : ¬ orderOf (5 : ZMod 449) ∣ 2 := fun h => mk 2 h h2
  have hmem : orderOf (5 : ZMod 449) ∈ Nat.divisors 14 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 14 = {1, 2, 7, 14} := by decide
  generalize ho : orderOf (5 : ZMod 449) = v at hdvd n7 n2 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 14 := by
    fin_cases hmem
    · exact absurd (⟨7, by norm_num⟩ : (1 : Nat) ∣ 7) n7
    · exact absurd (⟨1, by norm_num⟩ : (2 : Nat) ∣ 2) n2
    · exact absurd (⟨1, by norm_num⟩ : (7 : Nat) ∣ 7) n7
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
