-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.shared_time_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:23:40.38331+00:00
-- url     : https://prove2.me/submissions/bfdb1889-d493-4d3b-9ec4-479ffe080389

import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Theorems.Thm_ThreeSum_SharedReportingCosts_budget_powerBound
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_powerBound_mono
import Theorems.Thm_ThreeSum_SharedReportingCosts_shared_time_le


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Filter Real Scales Parameters StageBounds ArithmeticStageBounds
open scoped Topology
set_option maxHeartbeats 1500000
noncomputable section
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution : PowerBound sharedTime (2-epsilon*boxSaving) :=
  powerBound_mono budget_powerBound (Eventually.of_forall shared_time_le)
end ThreeSum.SharedReportingCosts
