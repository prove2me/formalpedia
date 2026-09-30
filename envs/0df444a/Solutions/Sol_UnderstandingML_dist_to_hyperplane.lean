-- Prove2me | solution 1 for UnderstandingML.dist_to_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:12:16.377905+00:00
-- url     : https://prove2.me/submissions/7beeaf6b-86a5-466f-9416-b3cd82b8485e

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} (w : Vec d) (hw : ‖w‖ = 1) (b : ℝ) (x : Vec d) :
    Metric.infDist x {v : Vec d | ⟪w, v⟫_ℝ + b = 0} = |⟪w, x⟫_ℝ + b| := by
  set c := ⟪w, x⟫_ℝ + b with hc
  have hww : ⟪w, w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hp : x - c • w ∈ {v : Vec d | ⟪w, v⟫_ℝ + b = 0} := by
    simp only [Set.mem_ofPred_eq, inner_sub_right, inner_smul_right, hww, mul_one]
    rw [hc]; ring
  apply le_antisymm
  · calc Metric.infDist x {v : Vec d | ⟪w, v⟫_ℝ + b = 0} ≤ dist x (x - c • w) :=
          Metric.infDist_le_dist_of_mem hp
      _ = |c| := by rw [dist_eq_norm, sub_sub_cancel, norm_smul, hw, mul_one, Real.norm_eq_abs]
  · rw [Metric.le_infDist ⟨_, hp⟩]
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    have : c = ⟪w, x - v⟫_ℝ := by rw [inner_sub_right, hc]; linarith
    rw [this, dist_eq_norm]
    calc |⟪w, x - v⟫_ℝ| ≤ ‖w‖ * ‖x - v‖ := abs_real_inner_le_norm _ _
      _ = ‖x - v‖ := by rw [hw, one_mul]
