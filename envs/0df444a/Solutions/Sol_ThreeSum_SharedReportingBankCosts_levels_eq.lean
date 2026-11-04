-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.levels_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:12:54.688542+00:00
-- url     : https://prove2.me/submissions/81fcb2b6-3289-4416-be23-fb69450ea497

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.SharedReportingBankCosts
theorem _root_.solution (n : ℕ) : SharedReportingBankHeader.levels (blocks n)=Switch.terminalDepth n+1 := rfl
end ThreeSum.SharedReportingBankCosts
