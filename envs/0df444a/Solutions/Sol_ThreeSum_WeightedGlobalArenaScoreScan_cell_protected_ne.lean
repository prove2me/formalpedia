-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.cell_protected_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:37:02.730056+00:00
-- url     : https://prove2.me/submissions/fdb2fdeb-b2a5-476e-8244-a05bd04999da

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_ge

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution {I : Input} {c i x : ℕ}
    (hc : c < 4) (hi : i < I.capacity) (hx : Protected I x) : x≠cell I c i := by
  have hlo := Nat.mul_le_mul_right I.capacity (show 9 ≤ 9+c by omega)
  have hhi := Nat.mul_le_mul_right I.capacity (show 10+c ≤ 13 by omega)
  have ha := cell_lt (I:=I) (c:=c) hi
  have hb := cell_ge I c i
  rcases hx with ⟨hx,_,_⟩
  unfold addr at *
  omega
end ThreeSum.WeightedGlobalArenaScoreScan
