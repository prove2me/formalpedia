-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumeration.layers_eq_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:56:56.483197+00:00
-- url     : https://prove2.me/submissions/39513009-f230-4988-943f-b9979f6f64e7

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
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
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetEnumeration
theorem _root_.solution (L j : ℕ) : layers L (j+1) = enumerateThrough L j := by
  induction j with
  | zero => simp [layers,enumerateThrough]
  | succ j ih =>
    change layers L (j+1) ++ enumerateLayer L (j+1) = _
    rw [ih]
    rfl
end ThreeSum.LightDownsetEnumeration
