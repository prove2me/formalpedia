-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:21:06.544294+00:00
-- url     : https://prove2.me/submissions/25b41e64-87f5-4673-843a-911a91d5453c

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
theorem _root_.solution (I : Input) (values : ℕ→Fin 4→ℤ) (μ : ℕ→ℤ) :
    Invariant I values μ 0 μ := by
  exact ⟨fun _ _ => rfl, fun _ h => by omega⟩
end ThreeSum.WeightedGlobalArenaScoreScan
