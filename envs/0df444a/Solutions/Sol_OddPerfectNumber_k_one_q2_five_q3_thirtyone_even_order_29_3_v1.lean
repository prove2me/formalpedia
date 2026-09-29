-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_even_order_29_3_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:10:10.200697+00:00
-- url     : https://prove2.me/submissions/c8e181fb-178a-4e75-8733-c7926127c82b

import Mathlib

theorem solution : Even (orderOf (3 : ZMod 29)) ∧ orderOf (3 : ZMod 29) = 28 := by
  have h28 : (3 : ZMod 29) ^ 28 = 1 := by decide
  have e14 : (3 : ZMod 29) ^ 14 ≠ 1 := by decide
  have e4 : (3 : ZMod 29) ^ 4 ≠ 1 := by decide
  have hdvd : orderOf (3 : ZMod 29) ∣ 28 := orderOf_dvd_of_pow_eq_one h28
  have hmem : orderOf (3 : ZMod 29) ∈ Nat.divisors 28 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 28 = {1, 2, 4, 7, 14, 28} := by decide
  rw [hfin] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h
  · have hd : orderOf (3 : ZMod 29) ∣ 14 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e14
  · have hd : orderOf (3 : ZMod 29) ∣ 14 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e14
  · have hd : orderOf (3 : ZMod 29) ∣ 4 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e4
  · have hd : orderOf (3 : ZMod 29) ∣ 14 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e14
  · have hd : orderOf (3 : ZMod 29) ∣ 14 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e14
  · exact ⟨h.symm ▸ ⟨14, by norm_num⟩, h⟩
