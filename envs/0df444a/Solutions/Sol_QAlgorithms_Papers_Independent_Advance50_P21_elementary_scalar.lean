-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P21.elementary_scalar
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:58:06.672035+00:00
-- url     : https://prove2.me/submissions/db8eb3e3-c330-4cd5-8543-39ddf0ef2326

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P21 in
theorem solution (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    min x y ≤ x * y + Real.sqrt (x * (1 - x) * y * (1 - y)) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    have h1 : 0 ≤ x * (1 - y) := mul_nonneg hx0 (by linarith)
    have h2 : (x * (1 - y)) ^ 2 ≤ x * (1 - x) * y * (1 - y) := by
      nlinarith [mul_nonneg h1 (sub_nonneg.2 h)]
    have h3 : x * (1 - y) ≤ Real.sqrt (x * (1 - x) * y * (1 - y)) := by
      rw [← Real.sqrt_sq h1]
      exact Real.sqrt_le_sqrt h2
    linarith
  · rw [min_eq_right h]
    have h1 : 0 ≤ y * (1 - x) := mul_nonneg hy0 (by linarith)
    have h2 : (y * (1 - x)) ^ 2 ≤ x * (1 - x) * y * (1 - y) := by
      nlinarith [mul_nonneg h1 (sub_nonneg.2 h)]
    have h3 : y * (1 - x) ≤ Real.sqrt (x * (1 - x) * y * (1 - y)) := by
      rw [← Real.sqrt_sq h1]
      exact Real.sqrt_le_sqrt h2
    linarith

end
