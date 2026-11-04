-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.half_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:32:16.668128+00:00
-- url     : https://prove2.me/submissions/579d42f8-03c5-4886-8b22-ee94f86b5b16

import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Theorems.Thm_ThreeSum_SharedReportingCosts_bits_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_powerBound_mono
import Theorems.Thm_ThreeSum_LightScales_microHalf_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Filter Real Scales Parameters StageBounds ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1500000
noncomputable section
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution : PowerBound half 0 :=
  powerBound_mono bits_powerBound (Eventually.of_forall fun n =>
    LightScales.microHalf_le_self (inputBits n))
end ThreeSum.SharedReportingCosts
