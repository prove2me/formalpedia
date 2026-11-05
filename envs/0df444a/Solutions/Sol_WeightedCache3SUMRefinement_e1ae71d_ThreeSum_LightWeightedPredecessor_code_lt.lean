-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor.code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:59.691652+00:00
-- url     : https://prove2.me/submissions/fc74b6ad-6823-470e-98af-701d31fec61f

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUM_Alias_88b09a412b2c33a9
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
theorem _root_.solution {N low high m : ℕ} (hm : m<2^(2*N)) :
    code N low high m<2^(2*N) := by
  unfold code LightTernaryCodes.zeroCode LightTernaryCodes.oneCode
  split_ifs
  · exact (eraseMask_le ((eraseMask_le hm).trans_lt hm)).trans_lt
      ((eraseMask_le hm).trans_lt hm)
  · exact (eraseMask_le hm).trans_lt hm
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessor
