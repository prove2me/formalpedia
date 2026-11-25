-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.sqrt_mem_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:10.990208+00:00
-- url     : https://prove2.me/submissions/86c42a00-3272-45e6-91d9-09a7b99bc67b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_natCast_Cl_of_not_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqrt_mem
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
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : ℂ_[l]}
    (hs : s ^ 2 = -(d : ℂ_[l])) : s ∈ MaximalUnramifiedExtension l := by
  have hd : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd (l := l) hld
  have hc : -(d : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    first
    | exact neg_mem (natCast_mem (MaximalUnramifiedExtension l) d)
    | exact neg_mem (by simpa using SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) (d : ℚ))
  have h2 : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs, norm_neg, hd]
  have hy : ‖s‖ = 1 := by
    have h0 := norm_nonneg s
    nlinarith [h2, h0]
  exact sqrt_mem (l := l) hl (-(d : ℂ_[l])) s hc hy hs
end ReciprocityTheory.ChartRestriction.L1
