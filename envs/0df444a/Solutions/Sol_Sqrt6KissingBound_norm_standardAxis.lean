-- Prove2me | solution 1 for Sqrt6KissingBound.norm_standardAxis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:30.284617+00:00
-- url     : https://prove2.me/submissions/142bffb4-3c17-4414-8cff-02b159e3e594

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Theorems.Thm_Sqrt6KissingBound_norm_sq_standardCoordinates

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) : ‖standardAxis d‖ = 1 := by
  have hsq : ‖standardAxis d‖ ^ 2 = 1 := by
    simpa [standardAxis] using
      norm_sq_standardCoordinates d 1 (0 : Fin d → ℝ)
  have hn : 0 ≤ ‖standardAxis d‖ := norm_nonneg _
  nlinarith
end Sqrt6KissingBound
