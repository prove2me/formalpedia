-- Prove2me | solution 1 for ThreeSum.MaskUnion.scanSet_mask_succ_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:17.32049+00:00
-- url     : https://prove2.me/submissions/6bca1ace-a9dc-4a67-a63f-2e68820e7fa9

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskUnion
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_succ_mem
import Theorems.Thm_ThreeSum_MaskUnion_current_mem_iff
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sum


set_option autoImplicit false
open ThreeSum ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskUnion
theorem _root_.solution {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) (ha : (⟨j,hj⟩ : Fin W) ∉ A) :
    subsetMask (scanSet A B (j+1)) = subsetMask (scanSet A B j)+2^j := by
  have hn : (⟨j,hj⟩ : Fin W) ∉ scanSet A B j := fun h => ha ((current_mem_iff A B hj).mp h)
  rw [scanSet_succ_mem A B hj hb,MaskDifference.subsetMask_sum,Finset.sum_insert hn,
    MaskDifference.subsetMask_sum]
  exact Nat.add_comm _ _
end ThreeSum.MaskUnion
