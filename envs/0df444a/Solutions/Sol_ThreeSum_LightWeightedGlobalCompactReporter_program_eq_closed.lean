-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalCompactReporter.program_eq_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:23:03.738368+00:00
-- url     : https://prove2.me/submissions/20ccbdcf-e397-4c0a-9ef4-4f873d41c6ac

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_driver_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalMomentReporter_program_eq_closed
attribute [local simp] ThreeSum.LightWeightedGlobalMomentReporter.driver_length



set_option autoImplicit false
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
open ThreeSum ThreeSum.LightWeightedGlobalCompactReporter
open Light TernaryMomentSchedule
namespace ThreeSum.LightWeightedGlobalCompactReporter
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H = closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by
  unfold program closedProgram
  rw [LightWeightedGlobalMomentReporter.program_eq_closed,LightWeightedGlobalMomentReporter.driver_length]
end ThreeSum.LightWeightedGlobalCompactReporter
