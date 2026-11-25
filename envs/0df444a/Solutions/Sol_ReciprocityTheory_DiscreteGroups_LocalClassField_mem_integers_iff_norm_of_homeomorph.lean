-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_integers_iff_norm_of_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:13.668037+00:00
-- url     : https://prove2.me/submissions/ddfcb138-46ed-4b19-b86b-f92cf23f561d

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_valuation_lt_one_iff_topologically_nilpotent
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
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {L : Type} [NormedField L] (e : K ≃+* L) (he : IsHomeomorph e) (x : K) :
    x ∈ 𝒪[K] ↔ ‖e x‖ ≤ 1 := by
  have key : ∀ y : K, valuation K y < 1 ↔ ‖e y‖ < 1 := by
    intro y
    rw [valuation_lt_one_iff_topologically_nilpotent, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h0 : 𝓝 (0 : K) = comap e (𝓝 0) := by
      rw [← map_zero e]; exact he.isInducing.nhds_eq_comap 0
    rw [h0, tendsto_comap_iff]
    refine tendsto_congr fun n => ?_
    simp
  rw [Valuation.mem_integer_iff]
  by_cases hx : x = 0
  · subst hx; simp
  have h := key x⁻¹
  rw [map_inv₀, map_inv₀, norm_inv] at h
  have hv : 0 < valuation K x := zero_lt_iff.2 (by simpa using hx)
  have hn : 0 < ‖e x‖ := by rw [norm_pos_iff]; simpa using hx
  rw [inv_lt_one₀ hv, inv_lt_one₀ hn] at h
  rw [← not_lt, ← not_lt, h]
end ReciprocityTheory.DiscreteGroups.LocalClassField
