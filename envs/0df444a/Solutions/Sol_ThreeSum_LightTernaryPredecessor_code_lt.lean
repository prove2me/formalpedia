-- Prove2me | solution 1 for ThreeSum.LightTernaryPredecessor.code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:01:41.798339+00:00
-- url     : https://prove2.me/submissions/058e5661-6d8e-451c-8935-e788109469f6

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_WeightedCache3SUM_Alias_88b09a412b2c33a9
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThreeSum.LightTernaryPredecessor
theorem _root_.solution {N low high m : ℕ} (hm : m<2^(2*N)) :
    code N low high m<2^(2*N) := by
  unfold code LightTernaryCodes.zeroCode LightTernaryCodes.oneCode
  split_ifs
  · exact (eraseMask_le ((eraseMask_le hm).trans_lt hm)).trans_lt
      ((eraseMask_le hm).trans_lt hm)
  · exact (eraseMask_le hm).trans_lt hm
end ThreeSum.LightTernaryPredecessor
