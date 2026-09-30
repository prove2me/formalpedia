-- Prove2me | solution 1 for UnderstandingML.hinge_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:11:41.410772+00:00
-- url     : https://prove2.me/submissions/29a53c38-218c-46ea-93ff-b494faba6eeb

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} (x : Vec d) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    ∀ w₁ w₂ : Vec d, |hingeLoss w₁ (x, y) - hingeLoss w₂ (x, y)| ≤ ‖x‖ * ‖w₁ - w₂‖ := by
  intro w₁ w₂
  simp only [hingeLoss]
  have hy' : |y| = 1 := by rcases hy with rfl | rfl <;> simp
  calc |max 0 (1 - y * ⟪w₁, x⟫_ℝ) - max 0 (1 - y * ⟪w₂, x⟫_ℝ)|
      ≤ |(1 - y * ⟪w₁, x⟫_ℝ) - (1 - y * ⟪w₂, x⟫_ℝ)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ = |y| * |⟪w₁ - w₂, x⟫_ℝ| := by
        rw [inner_sub_left, ← abs_mul, ← abs_neg]; ring_nf
    _ ≤ ‖x‖ * ‖w₁ - w₂‖ := by
        rw [hy', one_mul, mul_comm]
        exact abs_real_inner_le_norm _ _
