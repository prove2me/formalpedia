-- Prove2me | solution 1 for ThreeSum.ColorClassLists.bits_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:28.248591+00:00
-- url     : https://prove2.me/submissions/5cac78a8-d91b-4f38-b878-c13926ccadb2

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
theorem _root_.solution {n W : ℕ} (hn : n ≤ 2^W) :
    Function.Injective (fun i : Fin n => fun j : Fin W => i.val.testBit j.val) := by
  intro i j he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < W
  · exact congrFun he ⟨k,hk⟩
  · have hp : 2^W ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (i.isLt.trans_le (hn.trans hp)),
      Nat.testBit_eq_false_of_lt (j.isLt.trans_le (hn.trans hp))]
end ThreeSum.ColorClassLists
