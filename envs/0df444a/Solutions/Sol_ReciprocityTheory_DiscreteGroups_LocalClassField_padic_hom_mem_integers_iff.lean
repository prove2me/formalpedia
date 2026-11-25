-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.padic_hom_mem_integers_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:10.586816+00:00
-- url     : https://prove2.me/submissions/b0e603dc-e994-4ddd-8829-a28011293076

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isClosed_valuation_integers
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_padic_hom_valuation_lt_one
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
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (f : ℚ_[p] →+* K) (hf : Continuous f) (x : ℚ_[p]) :
    f x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have hx0 : x ≠ 0 := by rintro rfl; simp at hc; linarith
    have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := padic_hom_valuation_lt_one f hf _ h1
    rw [Valuation.mem_integer_iff] at h
    have h3 : valuation K (f x * f x⁻¹) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h) h2
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one, map_one] at h3
    exact lt_irrefl _ h3
  · intro h
    have hcl : IsClosed {z : ℤ_[p] | f (z : ℚ_[p]) ∈ (𝒪[K] : Set K)} :=
      isClosed_valuation_integers.preimage (hf.comp continuous_subtype_val)
    have hall : ∀ z : ℤ_[p], f (z : ℚ_[p]) ∈ (𝒪[K] : Set K) := by
      intro z
      refine PadicInt.denseRange_intCast.induction_on (p := fun z : ℤ_[p] => f (z : ℚ_[p]) ∈ (𝒪[K] : Set K)) z hcl ?_
      intro n
      simp only [PadicInt.coe_intCast, map_intCast, SetLike.mem_coe]
      exact intCast_mem 𝒪[K] n
    exact hall ⟨x, h⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
