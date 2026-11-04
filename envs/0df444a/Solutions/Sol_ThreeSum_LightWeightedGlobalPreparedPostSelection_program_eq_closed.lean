-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPreparedPostSelection.program_eq_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:47:04.36944+00:00
-- url     : https://prove2.me/submissions/0f9915d0-88b6-4db1-9b88-9a44c6f07ace

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalCompactReporter_program_eq_closed
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_program_eq_closed
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_program_eq_closed
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalPostSelection.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalPreparedPostSelection
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H = closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by
  unfold program libraries closedProgram
  rw [LightWeightedGlobalPostSelection.program_eq_closed,LightWeightedGlobalPostSelection.libraries_length]
end ThreeSum.LightWeightedGlobalPreparedPostSelection
