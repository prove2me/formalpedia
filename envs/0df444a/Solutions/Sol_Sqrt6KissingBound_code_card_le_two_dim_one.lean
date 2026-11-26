-- Prove2me | solution 1 for Sqrt6KissingBound.code_card_le_two_dim_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:22:48.363739+00:00
-- url     : https://prove2.me/submissions/fdc42a3e-1467-40ba-ba67-628c4ea2768f

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_DimensionOne
import Theorems.Thm_Sqrt6KissingBound_unit_vector_dim_one_eq_axis_or_neg
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution
    (X : Finset (EuclideanSpace ℝ (Fin 1)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1) : X.card ≤ 2 := by
  classical
  have hsub : X ⊆ ({standardAxis 0, -standardAxis 0} :
      Finset (EuclideanSpace ℝ (Fin 1))) := by
    intro x hx
    rcases unit_vector_dim_one_eq_axis_or_neg x (hunit x hx) with h | h
    · simp [h]
    · simp [h]
  exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_insert_le (standardAxis 0) ({-standardAxis 0} : Finset (EuclideanSpace ℝ (Fin 1))))
end Sqrt6KissingBound
