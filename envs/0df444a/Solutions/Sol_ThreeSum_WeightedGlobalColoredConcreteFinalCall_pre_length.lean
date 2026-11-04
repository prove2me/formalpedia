-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredConcreteFinalCall.pre_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:58:36.683696+00:00
-- url     : https://prove2.me/submissions/6b295dd2-b780-48bd-bed7-96a9782f31c7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalColoredSolver_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScore_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalColorPreparation.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalColoredSolver.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalPostSelection.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalPreparedPostSelection.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalSeedScore.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length



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
theorem _root_.solution (P : Profile κ) : (pre P).length=252 :=
  LightWeightedGlobalColoredSolver.libraries_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
end ThreeSum.WeightedGlobalColoredConcreteFinalCall
