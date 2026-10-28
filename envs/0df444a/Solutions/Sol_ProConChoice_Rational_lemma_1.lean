-- Prove2me | solution 1 for ProConChoice.Rational.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:19:09.572992+00:00
-- url     : https://prove2.me/submissions/b7d9d5b3-d1e6-4fa3-ba08-e12cf2ee0191

import Mathlib

theorem solution (m n : ℕ) (r : Fin m → ℝ) (c : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ m)
    (hsum : ∑ i, r i = ∑ j, c j) :
    ∃ A : Matrix (Fin m) (Fin n) ℝ,
      (∀ i, ∑ j, A i j = r i) ∧ (∀ j, ∑ i, A i j = c j) ∧ (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) := by
  by_cases hT : ∑ i, r i = 0
  · have hr0 : ∀ i, r i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hr i).1)).1 hT i (Finset.mem_univ _)
    have hc0 : ∀ j, c j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hc j).1)).1 (hsum ▸ hT) j (Finset.mem_univ _)
    refine ⟨0, ?_, ?_, ?_⟩ <;> simp [hr0, hc0]
  · have hTpos : 0 < ∑ i, r i :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => (hr i).1) (Ne.symm hT)
    set T := ∑ i, r i with hTdef
    refine ⟨fun i j => r i * c j / T, ?_, ?_, ?_⟩
    · intro i
      rw [← Finset.sum_div, ← Finset.mul_sum, ← hsum]
      field_simp
    · intro j
      rw [← Finset.sum_div, ← Finset.sum_mul, ← hTdef]
      field_simp
    · intro i j
      have hcj : c j ≤ T := hsum ▸ Finset.single_le_sum (f := c) (fun j _ => (hc j).1) (Finset.mem_univ j)
      refine ⟨div_nonneg (mul_nonneg (hr i).1 (hc j).1) hTpos.le, ?_⟩
      rw [div_le_one hTpos]
      calc r i * c j ≤ 1 * T := mul_le_mul (hr i).2 hcj (hc j).1 zero_le_one
        _ = T := one_mul _
