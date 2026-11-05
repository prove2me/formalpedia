-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan.cell_protected_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:04.96922+00:00
-- url     : https://prove2.me/submissions/899ccd62-ce09-4582-903b-85323be89ee6

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_cell_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_cell_ge

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution {I : Input} {c i x : ℕ}
    (hc : c < 4) (hi : i < I.capacity) (hx : Protected I x) : x≠cell I c i := by
  have hlo := Nat.mul_le_mul_right I.capacity (show 9 ≤ 9+c by omega)
  have hhi := Nat.mul_le_mul_right I.capacity (show 10+c ≤ 13 by omega)
  have ha := cell_lt (I:=I) (c:=c) hi
  have hb := cell_ge I c i
  rcases hx with ⟨hx,_,_⟩
  unfold addr at *
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
