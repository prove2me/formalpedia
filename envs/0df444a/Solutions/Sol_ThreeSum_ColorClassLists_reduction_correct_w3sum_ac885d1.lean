-- Prove2me | solution 1 for ThreeSum.ColorClassLists.reduction_correct_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:28.886611+00:00
-- url     : https://prove2.me/submissions/e02abbef-9dd8-4c9c-aa63-5184702f4be7

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_ColorClassLists_witness_iff
import Theorems.Thm_ThreeSum_ColorClassLists_bits_injective
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Coloring_exists_separating_parameter
import Theorems.Thm_ThreeSum_Coloring_mem_negValues
import Theorems.Thm_ThreeSum_Coloring_mem_values
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
theorem _root_.solution {n W : ℕ} (x : Fin n → ℤ) (hn : n ≤ 2^W) :
    Coloring.DistinctZeroSum x ↔ ∃ p : Coloring.Parameter W, witness p x := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hsum⟩
    obtain ⟨p,hi,hj,hk⟩ := Coloring.exists_separating_parameter
      (fun he => hij (bits_injective hn he)) (fun he => hik (bits_injective hn he))
      (fun he => hjk (bits_injective hn he))
    refine ⟨p,(witness_iff p x).mpr ?_⟩
    refine ⟨x i,(Coloring.mem_values x (indexColor p) 0 _).mpr ⟨i,hi,rfl⟩,
      x j,(Coloring.mem_values x (indexColor p) 1 _).mpr ⟨j,hj,rfl⟩,
      -x k,(Coloring.mem_negValues x (indexColor p) _).mpr ⟨k,hk,rfl⟩,?_⟩
    omega
  · rintro ⟨p,hp⟩
    obtain ⟨a,ha,b,hb,c,hc,he⟩ := (witness_iff p x).mp hp
    obtain ⟨i,hi,rfl⟩ := (Coloring.mem_values x (indexColor p) 0 a).mp ha
    obtain ⟨j,hj,rfl⟩ := (Coloring.mem_values x (indexColor p) 1 b).mp hb
    obtain ⟨k,hk,rfl⟩ := (Coloring.mem_negValues x (indexColor p) c).mp hc
    exact ⟨i,j,k,by intro heq; subst j; simp_all,
      by intro heq; subst k; simp_all,
      by intro heq; subst k; simp_all,by omega⟩
end ThreeSum.ColorClassLists
