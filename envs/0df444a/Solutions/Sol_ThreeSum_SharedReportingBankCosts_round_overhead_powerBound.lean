-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.round_overhead_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:36:10.985239+00:00
-- url     : https://prove2.me/submissions/2ba13300-683f-4ace-bae2-35d25790c1d6

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_round_extra_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_06d5b4aa2e4902bd
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
noncomputable section
namespace ThreeSum.SharedReportingBankCosts
theorem _root_.solution : PowerBound roundOverhead 0 :=
  SharedReportingCosts.overhead_powerBound.add_same round_extra_powerBound
end ThreeSum.SharedReportingBankCosts
