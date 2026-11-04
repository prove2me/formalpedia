-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPostSelection.args_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:16:29.804882+00:00
-- url     : https://prove2.me/submissions/3bce4c63-7cfe-4d09-8f16-8baa032eda12

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
    (args S c scratch matrix).length = 148 := rfl
end ThreeSum.LightWeightedGlobalPostSelection
