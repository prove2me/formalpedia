-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:09:42.128108+00:00
-- url     : https://prove2.me/submissions/2d7f59a1-6c35-4351-811e-8e0bc1fa2a22

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_WeightedCache3SUM_Alias_88b09a412b2c33a9
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_ne_iff
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskErase
theorem _root_.solution {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) < subsetMask s ↔ a ∈ s := by
  have hb := eraseMask_le (a := a.val) (subsetMask_isMask s).1
  rw [lt_iff_le_and_ne]
  simpa only [hb, true_and] using eraseMask_ne_iff s a
end ThreeSum.MaskErase
