-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.cell_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:17:28.057123+00:00
-- url     : https://prove2.me/submissions/750a0839-a92a-44ad-8ad2-508bc33d9cd9

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_offset_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution {I : Input} {c i : ℕ} (hi : i < I.capacity) :
    cell I c i < addr I.free I.capacity (10+c) := by
  have hh := offset_lt (free:=I.free) (C:=I.capacity) (slot:=9+c) (len:=I.capacity) hi le_rfl
  rw [show 9+c+1=10+c by omega] at hh
  exact hh
end ThreeSum.WeightedGlobalArenaScoreScan
