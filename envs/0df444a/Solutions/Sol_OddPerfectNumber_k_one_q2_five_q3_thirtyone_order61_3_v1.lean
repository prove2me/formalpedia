-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_order61_3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T12:35:48.538198+00:00
-- url     : https://prove2.me/submissions/659fd812-6834-4a7c-8866-7a56464df678

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 61) = 10 := by
  have hN : (3 : ZMod 61) ^ 10 = 1 := by decide
  have hn5 : (3 : ZMod 61) ^ 5 ≠ 1 := by decide
  have hn2 : (3 : ZMod 61) ^ 2 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 61) ∣ 10 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (3 : ZMod 61) ∣ k → (3 : ZMod 61) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 61)
    have hcon : (3 : ZMod 61) ^ (orderOf (3 : ZMod 61) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n5 : ¬ orderOf (3 : ZMod 61) ∣ 5 := fun h => mk 5 h hn5
  have n2 : ¬ orderOf (3 : ZMod 61) ∣ 2 := fun h => mk 2 h hn2
  have hmem : orderOf (3 : ZMod 61) ∈ Nat.divisors 10 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 10 = {1, 2, 5, 10} := by decide
  generalize ho : orderOf (3 : ZMod 61) = o at hdvd hn5 hn2 n5 n2 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨5, by norm_num⟩ : (1 : Nat) ∣ 5) n5
  · exact absurd (⟨1, by norm_num⟩ : (2 : Nat) ∣ 2) n2
  · exact absurd (⟨1, by norm_num⟩ : (5 : Nat) ∣ 5) n5
  · rfl
