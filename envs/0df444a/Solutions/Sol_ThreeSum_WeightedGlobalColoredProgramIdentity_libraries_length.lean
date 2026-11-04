-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredProgramIdentity.libraries_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:06:38.35938+00:00
-- url     : https://prove2.me/submissions/c5cacf94-80f6-4a92-a3cd-52be4d669a09

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
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
open ThreeSum ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredProgramIdentity
theorem _root_.solution (P : Profile κ) : (libraries P).length=252 := by
  unfold libraries
  exact LightWeightedGlobalColoredSolver.libraries_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
end ThreeSum.WeightedGlobalColoredProgramIdentity
