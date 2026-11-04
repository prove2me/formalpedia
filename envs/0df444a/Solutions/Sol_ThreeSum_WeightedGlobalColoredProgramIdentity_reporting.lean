-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredProgramIdentity.reporting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:37:25.426497+00:00
-- url     : https://prove2.me/submissions/70b246bf-22db-4ee4-a259-5ca7fc7b4374

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredProgramIdentity
theorem _root_.solution (P : Profile κ) (r : ℕ) (I : Input) :
    let S:=setup (r:=r) P.maps P.threshold P.cap P.output I
    WeightedGlobalExecutable.reporting P.maps P.cap P.K=
      LightWeightedGlobalPreparedPostSelection.closedProgram S.left.xs S.left.ys S.left.zs
        S.right.xs S.right.ys S.right.zs P.H := by
  rfl
end ThreeSum.WeightedGlobalColoredProgramIdentity
