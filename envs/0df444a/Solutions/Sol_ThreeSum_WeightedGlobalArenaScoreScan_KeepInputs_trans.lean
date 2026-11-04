-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.KeepInputs.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:19:19.69965+00:00
-- url     : https://prove2.me/submissions/01e03a8f-76f7-4c73-99ae-bc46a3e65359

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
namespace KeepInputs
theorem _root_.solution {I : Input} {μ ν ξ : ℕ→ℤ}
    (h : KeepInputs I μ ν) (g : KeepInputs I ν ξ) : KeepInputs I μ ξ :=
  fun x hx => (g x hx).trans (h x hx)
end KeepInputs
end ThreeSum.WeightedGlobalArenaScoreScan
