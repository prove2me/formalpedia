-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.cut_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:33:07.849107+00:00
-- url     : https://prove2.me/submissions/96f22f3a-5680-4fef-9802-1060e28a9866

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_residual_eq

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.SharedReportingBankCosts
theorem _root_.solution (n k : ℕ) :
    SharedReportingBankLevels.boxCut (half n) (blocks n) k=
      Switch.residualSize n k-Switch.actualSwitch n k := by
  unfold SharedReportingBankLevels.boxCut SharedReportingBankLevels.switch
  rw [residual_eq]
  rfl
end ThreeSum.SharedReportingBankCosts
