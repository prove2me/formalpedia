-- Prove2me | solution 1 for ThreeSum.WeightedPhysicalEuler.predCost_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:02:09.517197+00:00
-- url     : https://prove2.me/submissions/ab8b58e1-edff-4fcf-89d2-b85167118613

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
import Theorems.Thm_ThreeSum_LightWeightedCost_partialCost_address
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_code_canonical
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedPhysicalEuler
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) (hi : 0<(R i).val) :
    LightWeightedPredecessor.predCost N (LightWeightedEulerMetadata.lowAt N i.val)
      (LightWeightedEulerMetadata.highAt N i.val) (address R)=cacheCost (predecessor R i) := by
  unfold LightWeightedPredecessor.predCost
  change LightWeightedCost.partialCost N
    (LightWeightedPredecessor.code N (low i) (high i) (address R)) N=cacheCost (predecessor R i)
  rw [LightWeightedPredecessor.code_canonical R i hi,LightWeightedCost.partialCost_address]
end ThreeSum.WeightedPhysicalEuler
