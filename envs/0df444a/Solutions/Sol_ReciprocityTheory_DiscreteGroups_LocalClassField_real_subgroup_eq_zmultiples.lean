-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.real_subgroup_eq_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:49.790439+00:00
-- url     : https://prove2.me/submissions/5e4824ef-1b8f-4368-966a-0bef47c267f1

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_divHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_divHom_injective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_divHom_zmultiples
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_divHom_top
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (V : AddSubgroup ℝ) (h1 : (1 : ℝ) ∈ V) {e : ℕ}
    (hee : (AddSubgroup.zmultiples (1 : ℝ)).relIndex V = e) (he : 0 < e) :
    V = AddSubgroup.zmultiples ((e : ℝ)⁻¹) := by
  have he' : (e : ℝ) ≠ 0 := by positivity
  have hV : (V.comap (divHom e)).map (divHom e) = V := by
    rw [AddSubgroup.map_comap_eq, inf_eq_right]
    intro v hv
    have h2 := AddSubgroup.nsmul_relIndex_mem (AddSubgroup.zmultiples (1 : ℝ)) hv
    rw [hee] at h2
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h2
    refine ⟨k, ?_⟩
    rw [divHom_apply]
    have hk' : (k : ℝ) = e * v := by simpa using hk
    rw [hk']; field_simp
  have hle : AddSubgroup.zmultiples (e : ℤ) ≤ V.comap (divHom e) := by
    rw [← AddSubgroup.map_le_iff_le_comap, map_divHom_zmultiples he]
    exact AddSubgroup.zmultiples_le_of_mem h1
  have h3 : (AddSubgroup.zmultiples (e : ℤ)).relIndex (V.comap (divHom e)) = e := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (divHom_injective he), map_divHom_zmultiples he, hV, hee]
  have h4 := AddSubgroup.relIndex_mul_index hle
  rw [h3, Int.index_zmultiples, Int.natAbs_natCast] at h4
  have h5 : (V.comap (divHom e)).index = 1 := by
    have : e * (V.comap (divHom e)).index = e * 1 := by rw [h4, mul_one]
    exact Nat.eq_of_mul_eq_mul_left he this
  rw [AddSubgroup.index_eq_one] at h5
  rw [← hV, h5, map_divHom_top]
end ReciprocityTheory.DiscreteGroups.LocalClassField
