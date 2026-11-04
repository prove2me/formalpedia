-- Prove2me | solution 1 for ThreeSum.LightColorIndex.erase_eq_iff_testBit_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:15.557457+00:00
-- url     : https://prove2.me/submissions/24693724-ccb6-4b14-8bb4-a01d4cae03ff

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_ne_iff
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightColorIndex
theorem _root_.solution {W m : ℕ} (hm : m < 2^W) (i : Fin W) :
    MaskErase.eraseMask W i.val m = m ↔ m.testBit i.val = false := by
  have h := MaskErase.eraseMask_ne_iff (MaskDecode.decode W m) i
  rw [MaskDecode.subsetMask_decode hm] at h
  simp only [MaskDecode.decode,Finset.mem_filter,Finset.mem_univ,true_and,
    Nat.mem_bitIndices] at h
  cases hb : m.testBit i.val <;> simp_all
end ThreeSum.LightColorIndex
