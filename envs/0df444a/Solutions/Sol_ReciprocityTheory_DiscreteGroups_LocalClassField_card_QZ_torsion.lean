-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.card_QZ_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:05.43298+00:00
-- url     : https://prove2.me/submissions/15a1ea39-d74d-4fc9-91c2-6f63a7100d20

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (n : ℕ) (hn : 0 < n) : Nat.card {a : QZ // n • a = 0} = n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  let f : ℤ →+ QZ := (QuotientAddGroup.mk' (Int.castAddHom ℚ).range).comp
    ((AddMonoidHom.mulRight (1 / (n : ℚ))).comp (Int.castAddHom ℚ))
  have hf : ∀ k : ℤ, f k = QuotientAddGroup.mk ((k : ℚ) * (1 / (n : ℚ))) := fun _ => rfl
  have hker : f.ker = AddSubgroup.zmultiples (n : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, hf, QuotientAddGroup.eq_zero_iff, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hj' : (j : ℚ) = (k : ℚ) * (1 / (n : ℚ)) := hj
      have : (k : ℚ) = (n : ℚ) * j := by rw [hj']; field_simp
      exact_mod_cast this
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      show (j : ℚ) = (((n : ℤ) * j : ℤ) : ℚ) * (1 / (n : ℚ))
      push_cast
      field_simp
  have hr : ∀ a : QZ, n • a = 0 ↔ a ∈ f.range := by
    intro a
    constructor
    · intro ha
      obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective a
      have h1 : ((n • q : ℚ) : QZ) = 0 := ha
      rw [QuotientAddGroup.eq_zero_iff] at h1
      obtain ⟨j, hj⟩ := h1
      have hj' : (j : ℚ) = n • q := hj
      refine ⟨j, ?_⟩
      rw [hf, hj', nsmul_eq_mul]
      congr 1
      field_simp
    · rintro ⟨k, rfl⟩
      rw [hf]
      show ((n • ((k : ℚ) * (1 / (n : ℚ))) : ℚ) : QZ) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      refine ⟨k, ?_⟩
      show (k : ℚ) = n • ((k : ℚ) * (1 / (n : ℚ)))
      rw [nsmul_eq_mul]
      field_simp
  have hc : Nat.card f.range = n := by
    rw [← AddSubgroup.index_ker, hker, Int.index_zmultiples]
    simp
  exact (Nat.card_congr (Equiv.subtypeEquivRight hr)).trans hc
end ReciprocityTheory.DiscreteGroups.LocalClassField
