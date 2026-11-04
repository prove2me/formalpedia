-- Prove2me | solution 1 for ThreeSum.MaskDifference.subsetMask_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:32:39.458762+00:00
-- url     : https://prove2.me/submissions/390bba4c-5e48-49b7-8948-e4b3057cb288

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_injective
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty

set_option autoImplicit false
open ThreeSum ThreeSum.MaskDifference
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskDifference
theorem _root_.solution {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    exact subsetMask_injective L (h.trans (subsetMask_empty L).symm)
  · rintro rfl
    exact subsetMask_empty L
end ThreeSum.MaskDifference
