-- Prove2me | solution 1 for Sqrt6KissingBound.inner_standardAxis_standardCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:50.621003+00:00
-- url     : https://prove2.me/submissions/b8986b61-6af1-479b-b8ce-e288470bab1a

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.norm_standardAxis

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ)
    (t : ℝ) (v : Fin d → ℝ) :
    inner ℝ (standardAxis d) (standardCoordinates d (t, v)) = t := by
  simp [standardAxis, standardCoordinates, PiLp.inner_apply,
    Fin.sum_univ_succ] <;> simp
end Sqrt6KissingBound
