-- Prove2me | solution 1 for ThreeSum.LightColorParametersCosts.wordBudget_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:01:50.813214+00:00
-- url     : https://prove2.me/submissions/4ea01728-57be-40b2-8f85-ae5a2cdfd258

import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Theorems.Thm_ThreeSum_LightColorParametersCosts_width_powerBound
import Theorems.Thm_ThreeSum_LightColorParametersCosts_count_powerBound
import Theorems.Thm_ThreeSum_SharedReportingCosts_width_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const


set_option autoImplicit false
open ThreeSum ThreeSum.LightColorParametersCosts
open ColorParameters Scales StageBounds
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.LightColorParametersCosts
theorem _root_.solution : PowerBound wordBudget 0 :=
  (count_powerBound.add_same width_powerBound).add_same (PowerBound.const 10)
end ThreeSum.LightColorParametersCosts
