-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirtyone_even_order_29_331_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T15:10:25.902116+00:00
-- url     : https://prove2.me/submissions/0ed7e590-9767-4445-a9f9-170b56e0970a

import Mathlib

theorem solution : Even (orderOf (331 : ZMod 29)) ∧ orderOf (331 : ZMod 29) = 4 := by
  have h4 : (331 : ZMod 29) ^ 4 = 1 := by decide
  have e2 : (331 : ZMod 29) ^ 2 ≠ 1 := by decide
  have hdvd : orderOf (331 : ZMod 29) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hmem : orderOf (331 : ZMod 29) ∈ Nat.divisors 4 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hfin : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hfin] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · have hd : orderOf (331 : ZMod 29) ∣ 2 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e2
  · have hd : orderOf (331 : ZMod 29) ∣ 2 := h.symm ▸ by norm_num
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hd) e2
  · exact ⟨h.symm ▸ ⟨2, by norm_num⟩, h⟩
