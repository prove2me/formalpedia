-- Prove2me | solution 1 for PlanarRot90CoefficientUniqueness
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:04:24.881992+00:00
-- url     : https://prove2.me/submissions/05c6537b-dac3-4a80-bcbc-92fbb6382383

import Theorems.Thm_PlanarRot90Norm
import Theorems.Thm_PlanarRot90Orthogonal

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90CoefficientUniqueness]
theorem solution {d v : EuclideanSpace ℝ (Fin 2)}
    (hd : d ≠ 0) {a b : ℝ}
    (h : v = a • d + b • PlanarRot90 d) :
    a = inner ℝ v d / (‖d‖ ^ 2) ∧
      b = inner ℝ v (PlanarRot90 d) / (‖d‖ ^ 2) := by
  have horth := PlanarRot90Orthogonal d
  have horth' : inner ℝ (PlanarRot90 d) d = 0 := by
    simpa [real_inner_comm] using horth
  have hnormrot : ‖PlanarRot90 d‖ = ‖d‖ := PlanarRot90Norm d
  have hnormsq_ne : ‖d‖ ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hd))
  constructor
  · rw [h, inner_add_left, inner_smul_left, inner_smul_left]
    rw [horth']
    simp
    field_simp [hnormsq_ne]
  · rw [h, inner_add_left, inner_smul_left, inner_smul_left]
    rw [horth]
    rw [real_inner_self_eq_norm_sq, hnormrot]
    simp
    field_simp [hnormsq_ne]
