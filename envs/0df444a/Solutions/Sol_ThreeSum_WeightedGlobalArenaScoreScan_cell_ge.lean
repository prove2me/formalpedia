-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.cell_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:29:53.393444+00:00
-- url     : https://prove2.me/submissions/42770c06-d9eb-47f3-9f2f-9a70e40e325f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution (I : Input) (c i : ℕ) :
    addr I.free I.capacity (9+c) ≤ cell I c i := Nat.le_add_right _ _
end ThreeSum.WeightedGlobalArenaScoreScan
