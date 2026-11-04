-- Prove2me | solution 1 for ThreeSum.MaskDifference.subsetMask_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:24.367546+00:00
-- url     : https://prove2.me/submissions/56ab03d1-1d77-46e0-af94-33302ee2acd1

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sum
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskDifference
theorem _root_.solution (L : ℕ) : subsetMask (∅ : Finset (Fin L)) = 0 := by
  simp [subsetMask_sum]
end ThreeSum.MaskDifference
