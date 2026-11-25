-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.card_h2_trivial_int_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:37:20.737832+00:00
-- url     : https://prove2.me/submissions/0411b7d1-0287-4903-a64a-903f38f22299

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
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_nonempty_cyclic_even
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
theorem _root_.solution (C : Type) [Group C] [Finite C] [TopologicalSpace C] [IsTopologicalGroup C]
    [DiscreteTopology C] (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((trivRep C ℤ).H 2) = Nat.card C := by
  let _ : CommGroup C :=
    { (inferInstance : Group C) with
      mul_comm := fun a b => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
        rw [← zpow_add, ← zpow_add, add_comm] }
  let _ : Fintype C := Fintype.ofFinite C
  obtain ⟨e⟩ := nonempty_cyclic_even (trivRep C ℤ) g hg 2 two_ne_zero even_two
  rw [Nat.card_congr e.toEquiv]
  have hinv : ∀ k : ℤ, (k : (trivRep C ℤ).V) ∈ (trivRep C ℤ).rho.invariants := fun k _ => rfl
  let f : ℤ →+ ((trivRep C ℤ).rho.invariants ⧸
      (LinearMap.range (trivRep C ℤ).rho.norm).comap (trivRep C ℤ).rho.invariants.subtype) :=
    { toFun := fun k => Submodule.Quotient.mk ⟨k, hinv k⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hnorm : ∀ k : (trivRep C ℤ).V, (trivRep C ℤ).rho.norm k = ((Nat.card C : ℤ) * (show ℤ from k) : ℤ) := by
    intro k
    have h0 : ∀ g : C, (trivRep C ℤ).rho g k = k := fun _ => rfl
    rw [Representation.norm, LinearMap.sum_apply, Finset.sum_congr rfl (fun g _ => h0 g), Finset.sum_const,
      Finset.card_univ, Nat.card_eq_fintype_card]
    exact nsmul_eq_mul (Fintype.card C) (show ℤ from k)
  have hsurj : Surjective f := by
    intro y
    obtain ⟨⟨k, hk⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨k, rfl⟩
  have hker : f.ker = AddSubgroup.zmultiples (Nat.card C : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, Int.mem_zmultiples_iff]
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, ((hnorm j).symm.trans hj).symm⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (hnorm j).trans hj.symm⟩
  have h1 : Nat.card f.range = Nat.card C := by
    rw [← AddSubgroup.index_ker, hker, Int.index_zmultiples]
    simp
  rw [← h1, AddMonoidHom.range_eq_top.2 hsurj]
  exact (Nat.card_congr (Equiv.Set.univ _)).symm
end ReciprocityTheory.DiscreteGroups.LocalClassField
