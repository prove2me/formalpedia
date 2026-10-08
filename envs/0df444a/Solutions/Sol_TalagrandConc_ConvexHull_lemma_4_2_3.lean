-- Prove2me | solution 1 for TalagrandConc.ConvexHull.lemma_4_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:37:45.578658+00:00
-- url     : https://prove2.me/submissions/8ce07540-3d9d-4d87-8406-8eaf0fc15560

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic



namespace TalagrandConc.ConvexHull

lemma xi_one (α : ℝ) (hα : 0 < α) : xi α 1 = Real.log (1 + α) := by
  unfold xi
  have h1 : (1 + α - α * 1) / (1 + α) = (1 + α)⁻¹ := by
    field_simp; ring
  rw [h1, Real.log_inv]
  ring

lemma lemma_4_2_3_core (α a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    1 + α - α * a ≤ a ^ (-α) ∧ a + (1 - a) * Real.exp (xi α 1) ≤ a ^ (-α) := by
  have key : 1 + α - α * a ≤ a ^ (-α) := by
    rw [Real.rpow_def_of_pos ha]
    have h1 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha
    have h2 : 1 + (-α * Real.log a) ≤ Real.exp (-α * Real.log a) := Real.add_one_le_exp _ |>.trans_eq' (by ring)
    have h3 : Real.log a * -α = -α * Real.log a := by ring
    rw [h3]
    nlinarith
  refine ⟨key, ?_⟩
  rw [xi_one α hα, Real.exp_log (by linarith)]
  calc a + (1 - a) * (1 + α) = 1 + α - α * a := by ring
    _ ≤ a ^ (-α) := key

end TalagrandConc.ConvexHull

open TalagrandConc.ConvexHull


theorem solution (α a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    1 + α - α * a ≤ a ^ (-α) ∧ a + (1 - a) * Real.exp (xi α 1) ≤ a ^ (-α) := by
  exact lemma_4_2_3_core α a hα ha
