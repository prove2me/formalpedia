-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_span_singleton_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:40:23.775266+00:00
-- url     : https://prove2.me/submissions/46ecb3b6-b37f-47ee-ae73-e5666024b530

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
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
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (a b : OK p K) :
    a ∈ Ideal.span {b} ↔ ‖((a : K) : PadicAlgCl p)‖ ≤ ‖((b : K) : PadicAlgCl p)‖ := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have hc : ‖((c : K) : PadicAlgCl p)‖ ≤ 1 := (mem_OK_iff p K _).1 c.2
    show ‖((c : K) : PadicAlgCl p) * ((b : K) : PadicAlgCl p)‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  · intro h
    by_cases hb : ((b : K) : PadicAlgCl p) = 0
    · rw [hb, norm_zero] at h
      have ha : ((a : K) : PadicAlgCl p) = 0 := norm_le_zero_iff.1 h
      exact ⟨0, Subtype.ext (Subtype.ext (by rw [ha]; simp))⟩
    · have hb' : 0 < ‖((b : K) : PadicAlgCl p)‖ := norm_pos_iff.2 hb
      refine ⟨⟨(a : K) / (b : K), ?_⟩, Subtype.ext (Subtype.ext ?_)⟩
      · rw [mem_OK_iff]
        show ‖((a : K) : PadicAlgCl p) / ((b : K) : PadicAlgCl p)‖ ≤ 1
        rw [norm_div, div_le_one hb']
        exact h
      · show ((a : K) : PadicAlgCl p) / ((b : K) : PadicAlgCl p) * ((b : K) : PadicAlgCl p) = _
        rw [div_mul_cancel₀ _ hb]
end ReciprocityTheory.DiscreteGroups.LocalClassField
