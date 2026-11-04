-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPostABI.argv_zeroCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:13:14.578659+00:00
-- url     : https://prove2.me/submissions/04b821f5-faa8-46a8-90f1-f111043cb561

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_Light_Ends_set


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000
namespace ThreeSum.WeightedGlobalColoredPostABI
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) :
    (LightWeightedGlobalCompactReporter.zeroCounts S).argv=(S.argv.set 11 0).set 34 0 := by rfl
end ThreeSum.WeightedGlobalColoredPostABI
