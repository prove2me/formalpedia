-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrefixSeedHeader.prepared_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:48:30.447187+00:00
-- url     : https://prove2.me/submissions/50820109-ab2e-4d09-94ab-74eed8489308

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Theorems.Thm_ThreeSum_WeightedGlobalPrefixSeedHeader_result_seg
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_Light_Seg_of_sameOutside


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSeedHeader
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixStep LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalPrefixSeedHeader
theorem _root_.solution {X : Inputs} {μ ν : ℕ→ℤ} {xs : List ℤ}
    (H : Prepared X μ ν) (hs : Seg μ X.seed xs)
    (hbefore : X.seed+xs.length≤X.prefixFree) (hafter : X.liveHeader+106≤X.seed) :
    Seg ν X.seed (result xs X) :=by
  obtain ⟨μ₁,μ₂,_,_,_,hkeep,_,hsame,hν⟩:=H
  have hs₁:=hs.of_kept hkeep hbefore
  have hs₂:=hs₁.of_sameOutside hsame (Or.inr hafter)
  subst ν
  exact result_seg X hs₂
end ThreeSum.WeightedGlobalPrefixSeedHeader
