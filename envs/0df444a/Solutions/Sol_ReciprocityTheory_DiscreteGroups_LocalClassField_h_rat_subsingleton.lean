-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.h_rat_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:32.806106+00:00
-- url     : https://prove2.me/submissions/2a981201-0c4b-4583-a0e2-a8380396c0f7

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h_subsingleton_of_divisible
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
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
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
attribute [local simp] ReciprocityTheory.Coh.InflationTransgression.cj_coe



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((trivRep G ℚ).H n) := by
  refine h_subsingleton_of_divisible G (trivRep G ℚ) (fun k hk => ?_) n hn
  show Bijective fun m : ℚ => k • m
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun a b h => ?_, fun y => ⟨y / k, ?_⟩⟩
  · simpa [nsmul_eq_mul, hk'] using h
  · simp only [nsmul_eq_mul]; field_simp
end ReciprocityTheory.DiscreteGroups.LocalClassField
