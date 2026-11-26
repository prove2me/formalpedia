-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_upperBody4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:17:04.044067+00:00
-- url     : https://prove2.me/submissions/f10c9e0b-125e-4fa2-a796-f5583fea67e4

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_continuous_upperProfile4
import Theorems.Thm_Sqrt6KissingBound_measurableSet_rotationalProfile


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution : MeasurableSet upperBody4 :=
  measurableSet_rotationalProfile 3 measurableSet_Ioo continuous_upperProfile4.measurable
end Sqrt6KissingBound
