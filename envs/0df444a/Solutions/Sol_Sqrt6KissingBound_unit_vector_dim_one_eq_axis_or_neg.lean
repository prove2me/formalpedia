-- Prove2me | solution 1 for Sqrt6KissingBound.unit_vector_dim_one_eq_axis_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:16.822083+00:00
-- url     : https://prove2.me/submissions/c691d966-bb00-4cc6-b6c4-f897623195df

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_DimensionOne
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution
    (x : EuclideanSpace ℝ (Fin 1)) (hx : ‖x‖ = 1) :
    x = standardAxis 0 ∨ x = -standardAxis 0 := by
  have hs : (x 0) ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hx
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] using h
  have hf : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hcoord : x 0 = 1 := by linarith
    ext i
    fin_cases i
    simpa [standardAxis, standardCoordinates] using hcoord
  · right
    have hcoord : x 0 = -1 := by linarith
    ext i
    fin_cases i
    simpa [standardAxis, standardCoordinates] using hcoord
end Sqrt6KissingBound
