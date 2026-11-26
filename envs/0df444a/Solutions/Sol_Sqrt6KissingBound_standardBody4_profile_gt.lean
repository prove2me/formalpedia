-- Prove2me | solution 1 for Sqrt6KissingBound.standardBody4_profile_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:24:33.458642+00:00
-- url     : https://prove2.me/submissions/23adfc15-636c-4813-aa80-b776bb5d3623

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_sqrt3_lt_1351_div_780

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution :
    (33 : ℝ) / 1036 < (265352 - 153195 * s3_d4) / 320 := by
  nlinarith [sqrt3_lt_1351_div_780]
end Sqrt6KissingBound
