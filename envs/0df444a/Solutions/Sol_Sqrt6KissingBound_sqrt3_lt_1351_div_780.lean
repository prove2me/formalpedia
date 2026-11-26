-- Prove2me | solution 1 for Sqrt6KissingBound.sqrt3_lt_1351_div_780
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:23:10.077564+00:00
-- url     : https://prove2.me/submissions/e3737a3b-7bdf-4c1d-8f67-aa351d717b0b

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
private lemma s3_sq : s3_d4 ^ 2 = 3 := by norm_num [s3_d4]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution : s3_d4 < (1351 : ℝ) / 780 := by
  have hs0 : 0 ≤ s3_d4 := Real.sqrt_nonneg _
  have hq0 : 0 ≤ (1351 : ℝ) / 780 := by norm_num
  apply (sq_lt_sq₀ hs0 hq0).1
  rw [s3_sq]
  norm_num
end Sqrt6KissingBound
