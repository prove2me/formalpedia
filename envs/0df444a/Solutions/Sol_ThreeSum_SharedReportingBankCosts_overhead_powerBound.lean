-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.overhead_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:47:03.9702+00:00
-- url     : https://prove2.me/submissions/f4c00608-b59b-4935-8d1d-505fd3008161

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_round_overhead_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_setup_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
noncomputable section
namespace ThreeSum.SharedReportingBankCosts
theorem _root_.solution : PowerBound overhead 0 :=
  (round_overhead_powerBound.add_same (PowerBound.const 1600)).add_same setup_powerBound
end ThreeSum.SharedReportingBankCosts
