-- Prove2me | solution 1 for Sqrt6KissingBound.pi_lt_22_div_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:05.822657+00:00
-- url     : https://prove2.me/submissions/2ac96b97-0769-48e9-940c-242daf8babe6

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : Real.pi < (22 : ℝ) / 7 := by
  have h := Real.pi_lt_d4
  norm_num at h
  linarith
end Sqrt6KissingBound
