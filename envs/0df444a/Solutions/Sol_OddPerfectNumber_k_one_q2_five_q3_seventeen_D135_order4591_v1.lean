-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_order4591_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:06:22.027191+00:00
-- url     : https://prove2.me/submissions/90e8fdf3-5335-40c7-9c0e-c4e175a1cc89

import Mathlib

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem solution : orderOf (3 : ZMod 4591) = 270 := by
  have h270 : (3 : ZMod 4591) ^ 270 = 1 := by decide
  have h135 : (3 : ZMod 4591) ^ 135 ≠ 1 := by decide
  have h90 : (3 : ZMod 4591) ^ 90 ≠ 1 := by decide
  have h54 : (3 : ZMod 4591) ^ 54 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 4591) ∣ 270 := orderOf_dvd_of_pow_eq_one h270
  have mk : ∀ k : Nat, orderOf (3 : ZMod 4591) ∣ k →
      (3 : ZMod 4591) ^ k ≠ 1 → False := by
    intro k hdk hk
    obtain ⟨t, ht⟩ := hdk
    have hpow := pow_orderOf_eq_one (3 : ZMod 4591)
    have hcon : (3 : ZMod 4591) ^ (orderOf (3 : ZMod 4591) * t) = 1 := by
      rw [pow_mul, hpow, one_pow]
    rw [← ht] at hcon
    exact hk hcon
  have n135 : ¬ orderOf (3 : ZMod 4591) ∣ 135 := fun h => mk 135 h h135
  have n90 : ¬ orderOf (3 : ZMod 4591) ∣ 90 := fun h => mk 90 h h90
  have n54 : ¬ orderOf (3 : ZMod 4591) ∣ 54 := fun h => mk 54 h h54
  have hmem : orderOf (3 : ZMod 4591) ∈ Nat.divisors 270 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 270 = {1, 2, 3, 5, 6, 9, 10, 15, 18, 27, 30, 45, 54, 90, 135, 270} := by decide
  generalize ho : orderOf (3 : ZMod 4591) = o at hdvd n135 n90 n54 hmem ⊢
  rw [hfin] at hmem
  fin_cases hmem
  · exact absurd (⟨135, by norm_num⟩ : (1 : Nat) ∣ 135) n135
  · exact absurd (⟨45, by norm_num⟩ : (2 : Nat) ∣ 90) n90
  · exact absurd (⟨45, by norm_num⟩ : (3 : Nat) ∣ 135) n135
  · exact absurd (⟨27, by norm_num⟩ : (5 : Nat) ∣ 135) n135
  · exact absurd (⟨15, by norm_num⟩ : (6 : Nat) ∣ 90) n90
  · exact absurd (⟨15, by norm_num⟩ : (9 : Nat) ∣ 135) n135
  · exact absurd (⟨9, by norm_num⟩ : (10 : Nat) ∣ 90) n90
  · exact absurd (⟨9, by norm_num⟩ : (15 : Nat) ∣ 135) n135
  · exact absurd (⟨5, by norm_num⟩ : (18 : Nat) ∣ 90) n90
  · exact absurd (⟨5, by norm_num⟩ : (27 : Nat) ∣ 135) n135
  · exact absurd (⟨3, by norm_num⟩ : (30 : Nat) ∣ 90) n90
  · exact absurd (⟨3, by norm_num⟩ : (45 : Nat) ∣ 135) n135
  · exact absurd (⟨1, by norm_num⟩ : (54 : Nat) ∣ 54) n54
  · exact absurd (⟨1, by norm_num⟩ : (90 : Nat) ∣ 90) n90
  · exact absurd (⟨1, by norm_num⟩ : (135 : Nat) ∣ 135) n135
  · rfl
