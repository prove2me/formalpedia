-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPreparedPostSelection.args_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:28:37.427909+00:00
-- url     : https://prove2.me/submissions/d6ed2548-3835-4fc7-beca-ed3a84cf1528

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalPreparedPostSelection
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : Layout) (scratch matrix : ℕ) : (args S c scratch matrix).length = 148 := rfl
end ThreeSum.LightWeightedGlobalPreparedPostSelection
