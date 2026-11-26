-- Prove2me | solution 1 for Sqrt6KissingBound.standardCoordinates_mem_ball_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:07:50.022087+00:00
-- url     : https://prove2.me/submissions/26d69b85-881c-45d6-8e85-f3c861b024b4

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Theorems.Thm_Sqrt6KissingBound_norm_sq_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) (t : ℝ) (v : Fin d → ℝ) :
    standardCoordinates d (t, v) ∈ ball 0 1 ↔
      t ^ 2 + ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 < 1 := by
  rw [mem_ball, dist_zero_right]
  constructor
  · intro h
    let N : ℝ := ‖standardCoordinates d (t, v)‖
    have hN0 : 0 ≤ N := norm_nonneg _
    have hpos : 0 < (1 - N) * (1 + N) :=
      mul_pos (sub_pos.mpr h) (by linarith)
    have hsq : N ^ 2 < 1 := by nlinarith
    simpa [N, norm_sq_standardCoordinates] using hsq
  · intro h
    let N : ℝ := ‖standardCoordinates d (t, v)‖
    have hN0 : 0 ≤ N := norm_nonneg _
    have hsq : N ^ 2 < 1 := by
      simpa [N, norm_sq_standardCoordinates] using h
    by_contra hnot
    have hge : 1 ≤ N := le_of_not_gt hnot
    nlinarith [sq_nonneg (N - 1)]
end Sqrt6KissingBound
