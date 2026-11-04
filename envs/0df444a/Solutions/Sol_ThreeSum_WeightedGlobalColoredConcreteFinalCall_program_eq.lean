-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredConcreteFinalCall.program_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:45:16.71258+00:00
-- url     : https://prove2.me/submissions/2379cf8c-39f6-428b-88b4-3a544ccdaa47

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredConcreteFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalColoredFinalReady
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredConcreteFinalCall
theorem _root_.solution (P : Profile κ) : P.color=
    ReportingHostRelocation.program (pre P) (WeightedGlobalExecutable.reporting P.maps P.cap P.K)++suffix P :=rfl
end ThreeSum.WeightedGlobalColoredConcreteFinalCall
