-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.protected_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:18:22.716423+00:00
-- url     : https://prove2.me/submissions/f73de457-748b-4397-bda9-bad98d71d0b2

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
theorem _root_.solution {I : Input} {x : ℕ} (hx : x < addr I.free I.capacity 9)
    (hh : x≠addr I.free I.capacity 1+104) : Protected I x := by
  have hm := Nat.mul_le_mul_right I.capacity (show 9≤16 by omega)
  refine ⟨Or.inl hx,?_,hh⟩
  unfold addr at *
  omega
end ThreeSum.WeightedGlobalArenaScoreScan
