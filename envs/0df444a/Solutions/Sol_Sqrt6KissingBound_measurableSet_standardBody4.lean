-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_standardBody4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:22:14.872685+00:00
-- url     : https://prove2.me/submissions/0342c100-7250-41f2-b558-608dd0487e18

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBody4
import Theorems.Thm_Sqrt6KissingBound_measurableSet_lowerBicone


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution : MeasurableSet standardBody4 :=
  (measurableSet_lowerBicone 2).union measurableSet_upperBody4
end Sqrt6KissingBound
