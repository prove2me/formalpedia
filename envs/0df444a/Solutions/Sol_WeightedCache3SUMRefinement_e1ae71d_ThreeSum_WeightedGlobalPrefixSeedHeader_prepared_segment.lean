-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:42:17.131112+00:00
-- url     : https://prove2.me/submissions/f0e38b0f-bfe0-4a3e-971a-0500a9498f00

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixSeedHeader_result_seg
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_Light_Seg_of_sameOutside


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader
theorem _root_.solution {X : Inputs} {μ ν : ℕ→ℤ} {xs : List ℤ}
    (H : Prepared X μ ν) (hs : Seg μ X.seed xs)
    (hbefore : X.seed+xs.length≤X.prefixFree) (hafter : X.liveHeader+106≤X.seed) :
    Seg ν X.seed (result xs X) :=by
  obtain ⟨μ₁,μ₂,_,_,_,hkeep,_,hsame,hν⟩:=H
  have hs₁:=hs.of_kept hkeep hbefore
  have hs₂:=hs₁.of_sameOutside hsame (Or.inr hafter)
  subst ν
  exact result_seg X hs₂
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrefixSeedHeader
