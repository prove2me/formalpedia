-- Prove2me | solution 1 for ThreeSum.ColorParameters.parameter_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:35.1892+00:00
-- url     : https://prove2.me/submissions/10f8f51f-ee39-4f21-8a2e-4ad472d31478

import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Mathlib.Data.List.FinRange
import Definitions.Def_Submission_ThreeSum_ColorParameters
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
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
theorem _root_.solution {W : ℕ} (p : Coloring.Parameter W) : parameter (index_lt p)=p := by
  have hw : 0 < W := by have := p.1.1.isLt; omega
  have h0 := (p.2 (false,false)).isLt
  have h1 := (p.2 (false,true)).isLt
  have h2 := (p.2 (true,false)).isLt
  have h3 := (p.2 (true,true)).isLt
  have hq : index p/81=p.1.1.val*W+p.1.2.val := by unfold index; omega
  have hi : index p/81/W=p.1.1.val := by
    rw [hq,Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.div_eq_of_lt p.1.2.isLt]
    simp
  have hj : index p/81%W=p.1.2.val := by
    rw [hq,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt p.1.2.isLt]
  apply Prod.ext
  · exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  · funext xy
    rcases xy with ⟨x,y⟩
    cases x <;> cases y <;> apply Fin.ext <;> dsimp [parameter,colorMap] <;> unfold index <;> omega
end ThreeSum.ColorParameters
