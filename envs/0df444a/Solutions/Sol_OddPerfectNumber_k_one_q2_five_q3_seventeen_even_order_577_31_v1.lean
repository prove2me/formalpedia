-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_even_order_577_31_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:54:50.300719+00:00
-- url     : https://prove2.me/submissions/b790b10c-db69-4b4c-830d-118982fc6d72

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : Even (orderOf (31 : ZMod 577)) ∧ orderOf (31 : ZMod 577) = 18 := by
  have hN : (31 : ZMod 577) ^ 18 = 1 := by decide
  have h9 : (31 : ZMod 577) ^ 9 ≠ 1 := by decide
  have h6 : (31 : ZMod 577) ^ 6 ≠ 1 := by decide
  have hdvd : orderOf (31 : ZMod 577) ∣ 18 := orderOf_dvd_of_pow_eq_one hN
  have mk : ∀ k : Nat, orderOf (31 : ZMod 577) ∣ k →
      (31 : ZMod 577) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (31 : ZMod 577)
    have hcon : (31 : ZMod 577) ^ (orderOf (31 : ZMod 577) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n9 : ¬ orderOf (31 : ZMod 577) ∣ 9 := fun h => mk 9 h h9
  have n6 : ¬ orderOf (31 : ZMod 577) ∣ 6 := fun h => mk 6 h h6
  have hmem : orderOf (31 : ZMod 577) ∈ Nat.divisors 18 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 18 = {1, 2, 3, 6, 9, 18} := by decide
  generalize ho : orderOf (31 : ZMod 577) = v at hdvd n9 n6 hmem ⊢
  rw [hfin] at hmem
  have heq : v = 18 := by
    fin_cases hmem
    · exact absurd (⟨9, by norm_num⟩ : (1 : Nat) ∣ 9) n9
    · exact absurd (⟨3, by norm_num⟩ : (2 : Nat) ∣ 6) n6
    · exact absurd (⟨3, by norm_num⟩ : (3 : Nat) ∣ 9) n9
    · exact absurd (⟨1, by norm_num⟩ : (6 : Nat) ∣ 6) n6
    · exact absurd (⟨1, by norm_num⟩ : (9 : Nat) ∣ 9) n9
    · rfl
  exact ⟨by rw [heq]; decide, heq⟩
