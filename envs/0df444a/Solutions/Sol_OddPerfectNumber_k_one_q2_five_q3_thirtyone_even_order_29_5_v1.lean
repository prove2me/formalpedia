-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_even_order_29_5_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:10:14.598243+00:00
-- url     : https://prove2.me/submissions/741dfc3d-764e-463f-90c3-ec8dee35ecba

import Mathlib

theorem solution : Even (orderOf (5 : ZMod 29)) ∧ orderOf (5 : ZMod 29) = 14 := by
  have h14 : (5 : ZMod 29) ^ 14 = 1 := by decide
  have e7 : (5 : ZMod 29) ^ 7 ≠ 1 := by decide
  have e2 : (5 : ZMod 29) ^ 2 ≠ 1 := by decide
  have hdvd : orderOf (5 : ZMod 29) ∣ 14 := orderOf_dvd_of_pow_eq_one h14
  have hmem : orderOf (5 : ZMod 29) ∈ Nat.divisors 14 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 14 = {1, 2, 7, 14} := by decide
  rw [hfin] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · have hd : orderOf (5 : ZMod 29) ∣ 2 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e2
  · have hd : orderOf (5 : ZMod 29) ∣ 2 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e2
  · have hd : orderOf (5 : ZMod 29) ∣ 7 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e7
  · exact ⟨h.symm ▸ ⟨7, by norm_num⟩, h⟩
