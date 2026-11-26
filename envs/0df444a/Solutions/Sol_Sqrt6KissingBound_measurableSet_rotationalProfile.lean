-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_rotationalProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:55.151816+00:00
-- url     : https://prove2.me/submissions/e553ac00-80ce-4545-8c1a-f8f8a2450226

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Theorems.Thm_Sqrt6KissingBound_measurableSet_profileRegion

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet (rotationalProfile d s g) := by
  exact (measurableSet_profileRegion d hs hg).preimage
    (standardCoordinates d).symm.measurable
end Sqrt6KissingBound
