-- Prove2me | solution 1 for ThreeSum.ColorClassLists.mem_classList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:09.588846+00:00
-- url     : https://prove2.me/submissions/6fd73355-64f5-45ae-b436-7faaee910f40

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Coloring_mem_values
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Theorems.Thm_ThreeSum_LightClassFilter_mem_items
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
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.ColorClassLists.value_fin

set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter
namespace ThreeSum.ColorClassLists
theorem _root_.solution {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : Fin 3) (z : ℤ) :
    z ∈ classList p x c.val 1 ↔ z ∈ Coloring.values x (indexColor p) c := by
  rw [classList,mem_items,Coloring.mem_values]
  simp only [one_mul]
  constructor
  · rintro ⟨i,hi,hc,hx⟩
    refine ⟨⟨i,hi⟩,Fin.ext hc,?_⟩
    simpa only [← value_fin x ⟨i,hi⟩] using hx
  · rintro ⟨i,hc,hx⟩
    exact ⟨i.val,i.isLt,congrArg Fin.val hc,by simpa using hx⟩
end ThreeSum.ColorClassLists
