-- Prove2me | solution 1 for ThreeSum.ColorParameters.reduction_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:27.260062+00:00
-- url     : https://prove2.me/submissions/e4199655-090f-45c8-b47c-c4c3d34a48ab

import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Mathlib.Data.List.FinRange
import Definitions.Def_Submission_ThreeSum_ColorParameters
import Theorems.Thm_ThreeSum_ColorParameters_parameter_index
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_a2077ae4d725396c
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_Coloring_reduction_correct
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
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
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.ColorParameters
namespace ThreeSum.ColorParameters
theorem _root_.solution {n W : ℕ} (x : Fin n→ℤ) (hn : n ≤ 2^W) :
    Coloring.DistinctZeroSum x ↔
      ∃ t, ∃ ht : t < count W, ColorClassLists.witness (parameter ht) x := by
  rw [ColorClassLists.reduction_correct x hn]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨index p,index_lt p,by simpa only [parameter_index] using hp⟩
  · rintro ⟨t,ht,hp⟩
    exact ⟨parameter ht,hp⟩
end ThreeSum.ColorParameters
