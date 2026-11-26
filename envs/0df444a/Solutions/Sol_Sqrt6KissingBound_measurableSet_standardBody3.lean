-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_standardBody3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:24.208577+00:00
-- url     : https://prove2.me/submissions/259fe103-2e28-4217-aa4c-f26741d90a09

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBody3
import Theorems.Thm_Sqrt6KissingBound_measurableSet_lowerBicone


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution : MeasurableSet standardBody3 :=
  (measurableSet_lowerBicone 1).union measurableSet_upperBody3
end Sqrt6KissingBound
