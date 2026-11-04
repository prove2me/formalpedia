-- Prove2me | solution 1 for ThreeSum.LightWeightedPredecessor.predCost_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:22.7362+00:00
-- url     : https://prove2.me/submissions/43346170-821d-4a62-a6d7-dccb3dc84ab1

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Predecessor
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_code_canonical
import Theorems.Thm_ThreeSum_LightWeightedCost_partialCost_address
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedPredecessor
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N)
    (hi : 0<(R i).val) :
    predCost N (low i) (high i) (address R)=WeightedBankEnumeration.cacheCost (predecessor R i) := by
  unfold predCost
  rw [code_canonical R i hi,LightWeightedCost.partialCost_address]
end ThreeSum.LightWeightedPredecessor
