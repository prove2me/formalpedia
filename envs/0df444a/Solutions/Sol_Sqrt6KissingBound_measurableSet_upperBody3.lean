-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_upperBody3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:15:40.195936+00:00
-- url     : https://prove2.me/submissions/676f8106-3469-4abc-ad4b-f5767d6b4bcb

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_continuous_upperProfile3
import Theorems.Thm_Sqrt6KissingBound_measurableSet_rotationalProfile


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution : MeasurableSet upperBody3 :=
  measurableSet_rotationalProfile 2 measurableSet_Ioo continuous_upperProfile3.measurable
end Sqrt6KissingBound
