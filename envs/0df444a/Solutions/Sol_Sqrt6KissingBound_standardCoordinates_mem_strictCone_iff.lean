-- Prove2me | solution 1 for Sqrt6KissingBound.standardCoordinates_mem_strictCone_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:07:55.471642+00:00
-- url     : https://prove2.me/submissions/98b1ec24-ff62-4c71-bf5b-aac4a1b63549

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Theorems.Thm_Sqrt6KissingBound_norm_sq_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) (t : ℝ)
    (v : Fin d → ℝ) :
    standardCoordinates d (t, v) ∈ strictCone (standardAxis d) ↔
      (Real.sqrt 3 / 2) *
          Real.sqrt (t ^ 2 +
            ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2) < t := by
  change (Real.sqrt 3 / 2) * ‖standardCoordinates d (t, v)‖ <
    inner ℝ (standardAxis d) (standardCoordinates d (t, v)) ↔ _
  rw [inner_standardAxis_standardCoordinates]
  congr 2
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_standardCoordinates]
end Sqrt6KissingBound
