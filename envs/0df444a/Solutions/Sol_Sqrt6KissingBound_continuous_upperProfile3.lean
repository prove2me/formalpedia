-- Prove2me | solution 1 for Sqrt6KissingBound.continuous_upperProfile3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:14:23.905352+00:00
-- url     : https://prove2.me/submissions/a10a78d4-e209-4f8c-bf24-09753888dddc

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution : Continuous upperProfile3 := by
  unfold upperProfile3
  fun_prop
end Sqrt6KissingBound
