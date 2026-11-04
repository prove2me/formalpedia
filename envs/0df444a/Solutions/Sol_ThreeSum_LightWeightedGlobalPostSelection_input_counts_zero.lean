-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPostSelection.input_counts_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:16:00.321929+00:00
-- url     : https://prove2.me/submissions/d5720d5f-bce5-40fe-8ad5-96bc36d97f1c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed

set_option autoImplicit false
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
open ThreeSum ThreeSum.LightWeightedGlobalPostSelection
open Light TernaryMomentSchedule
namespace ThreeSum.LightWeightedGlobalPostSelection
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : LightOriginalSurvivorPair.Layout) (scratch matrix : ℕ) :
    (args S c scratch matrix).getD 34 0 = 0 ∧
    (args S c scratch matrix).getD 36 0 = 0 ∧
    (args S c scratch matrix).getD 53 0 = 0 ∧
    (args S c scratch matrix).getD 76 0 = 0 := by
  exact ⟨rfl,rfl,rfl,rfl⟩
end ThreeSum.LightWeightedGlobalPostSelection
