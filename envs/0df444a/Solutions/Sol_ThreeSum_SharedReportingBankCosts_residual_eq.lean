-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.residual_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:11:07.227209+00:00
-- url     : https://prove2.me/submissions/1d92f88e-1208-42fe-b4df-bc5a31774bd6

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
theorem _root_.solution (n k : ℕ) :
    SharedReportingBankLevels.residual (half n) (blocks n) k=Switch.residualSize n k := by
  unfold SharedReportingBankLevels.residual half blocks Switch.residualSize muZero microSize microHalf
  ring
end ThreeSum.SharedReportingBankCosts
