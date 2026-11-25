-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.h_subsingleton_of_uniquely_divisible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:35:39.038493+00:00
-- url     : https://prove2.me/submissions/eab7d756-237d-41d2-a639-6c90ba35fc2b

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Theorems.Thm_ReciprocityTheory_Coh_Cx_H_ind
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_ProjectiveLinePlaces_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_ProjectiveLinePlaces_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_finiteLevel_holds
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
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {R : Type} [CommRing R]
    (M : TRep R G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) := by
  suffices h : ∀ x : M.H n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨-, h⟩ := finiteLevel_holds R G M n x
  obtain ⟨k, hk, hkx⟩ := h hn
  let e : M.V ≃ₗ[R] M.V := LinearEquiv.ofBijective ((k : R) • LinearMap.id) (by
    have := hM k hk
    convert this using 2 with m
    simp [Nat.cast_smul_eq_nsmul])
  have he : ∀ m, e m = (k : R) • m := fun m => rfl
  let Q : Pair M M := Pair.ofMap e.symm.toLinearMap continuous_of_discreteTopology (by
    intro g m
    apply e.injective
    show e (e.symm _) = e (M.rho g (e.symm m))
    rw [e.apply_symm_apply, he, ← map_smul, ← he, e.apply_symm_apply])
  have hQ : ∀ y : M.H n, (k : R) • Q.hom.H n y = y := by
    intro y
    induction y using Cx.H_ind with
    | h c hc =>
      rw [Cx.Hom.H_cls, Cx.cls_smul]
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      exact e.apply_symm_apply _
  rw [← hQ x, ← map_smul, Nat.cast_smul_eq_nsmul, hkx, map_zero]
end ReciprocityTheory.DiscreteGroups.LocalClassField
