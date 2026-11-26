-- Prove2me | solution 1 for Sqrt6KissingBound.continuous_upperProfile4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:15:29.180795+00:00
-- url     : https://prove2.me/submissions/b54a6b6f-8e6e-43ce-9ff5-48e60e6a5229

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution : Continuous upperProfile4 := by
  unfold upperProfile4
  fun_prop
end Sqrt6KissingBound
