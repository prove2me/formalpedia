-- Prove2me | solution 1 for ThreeSum.ColorClassLists.witness_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:58.556413+00:00
-- url     : https://prove2.me/submissions/b26898ed-a5a8-468e-8fde-b1db8dbe76f8

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_ColorClassLists_mem_classList
import Theorems.Thm_ThreeSum_ColorClassLists_mem_negClassList
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
theorem _root_.solution {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    witness p x ↔ Coloring.ThreeSetWitness
      (Coloring.values x (indexColor p) 0) (Coloring.values x (indexColor p) 1)
      (Coloring.negValues x (indexColor p)) := by
  unfold witness Coloring.ThreeSetWitness
  have h0 (z : ℤ) : z ∈ classList p x 0 1 ↔ z ∈ Coloring.values x (indexColor p) 0 :=
    mem_classList p x (0 : Fin 3) z
  have h1 (z : ℤ) : z ∈ classList p x 1 1 ↔ z ∈ Coloring.values x (indexColor p) 1 :=
    mem_classList p x (1 : Fin 3) z
  simp only [h0,h1,mem_negClassList]
end ThreeSum.ColorClassLists
