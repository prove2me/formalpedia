-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.protected_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:27:15.416417+00:00
-- url     : https://prove2.me/submissions/7162c376-e427-4845-9e26-7ac972374aca

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
theorem _root_.solution {I : Input} {x : ℕ} (hx : addr I.free I.capacity 13≤x)
    (hy : x < addr I.free I.capacity 16) (hc : 106≤I.capacity) : Protected I x := by
  refine ⟨Or.inr hx,hy,?_⟩
  unfold addr at *
  nlinarith
end ThreeSum.WeightedGlobalArenaScoreScan
