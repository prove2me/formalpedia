-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredConcreteFinalCall.reporter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:38:22.720918+00:00
-- url     : https://prove2.me/submissions/e15f4993-65a6-4c4c-bde4-92fdb393d5aa

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredConcreteFinalCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalColoredFinalReady
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredConcreteFinalCall
theorem _root_.solution :
    let S:=WeightedGlobalArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
      (selected P n free menu c A B C initial)
    LightWeightedGlobalPreparedPostSelection.closedProgram
      S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs P.H=
        WeightedGlobalExecutable.reporting P.maps P.cap P.K :=rfl
end ThreeSum.WeightedGlobalColoredConcreteFinalCall
