-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPostABI.post_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:11:00.450435+00:00
-- url     : https://prove2.me/submissions/31de7e8d-6cb3-4a7d-ac6d-16167c530daa

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000
namespace ThreeSum.WeightedGlobalColoredPostABI
theorem _root_.solution : (postArgs.map Expr.cost).sum=671 := by rfl
end ThreeSum.WeightedGlobalColoredPostABI
