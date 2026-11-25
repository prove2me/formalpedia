-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inertKur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:38:15.516421+00:00
-- url     : https://prove2.me/submissions/06ffc669-12de-4a95-a85f-64cc195746ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModInertKur
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fixed_mem_Kur
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_locEmb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_locLift
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
theorem _root_.solution {d l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (x : Om d)
    (hx : ∀ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ → σ x = x) : ι (x : ℂ) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨e, he⟩ := locEmb d l ι
  have hs : (e (algebraMap (KQ d) (Om d) (sqK d))) ^ 2 = -(d : PadicAlgCl l) := by
    have h1 : (algebraMap (KQ d) (Om d) (sqK d)) ^ 2 = -(d : Om d) := by
      apply Subtype.ext
      simpa [sqK] using sqD_sq d
    rw [← map_pow, h1, map_neg, map_natCast]
  have hint : IsIntegral ℚ_[l] (e (algebraMap (KQ d) (Om d) (sqK d))) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ_[l]), Polynomial.monic_X_pow_add_C _ (by norm_num), ?_⟩
    simp [hs]
  have hK := IntermediateField.adjoin.finiteDimensional hint
  have hmem := fixed_mem_Kur _ hK (e x) (fun ρ hρ => by
    obtain ⟨σ, hσ, hc⟩ := locLift ι e he ρ hρ
    rw [← hc, hx σ hσ])
  rw [← he]
  exact kur_le hl hld hs hmem
end ReciprocityTheory.ChartRestriction.L1
