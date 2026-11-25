-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_comp_normHom_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:06.114989+00:00
-- url     : https://prove2.me/submissions/8bffe9ef-1933-49a8-a737-49bdbf8428b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbarRep_mul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbarRep_out
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finite_quot_of_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_tower_bijective
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
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') (y : KbarMult p) (hy : y ∈ multOf p L') :
    normHom p K L (normHom p L L' y) = normHom p K L' y := by
  have := finite_quot_of_le (p := p) (K := K) hL' h'
  have := finite_quot_of_le (p := p) (K := K) hL' (le_refl L')
  have := finite_quot_of_le (p := p) (K := L) hL' (le_refl L')
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  have := Fintype.ofFinite (GK p K ⧸ subG p K L')
  have := Fintype.ofFinite (GK p L ⧸ subG p L L')
  rw [normHom_apply, normHom_apply, normHom_apply]
  simp only [map_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_bijective _ (tower_bijective h h') _ _ fun x => ?_
  rw [kbarRep_out y hy, kbarRep_mul]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
