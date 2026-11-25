-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.norm0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:24.420154+00:00
-- url     : https://prove2.me/submissions/45906f75-dd80-47cb-88b5-4a5c681e80c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_cur_sub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_curried_coboundary_eq
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710
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
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_memB
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneDifferential_val
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution (hN : IsOpen (N : Set G)) (x : M.coch.X 2)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ m ∈ N, cur M (x - M.coch.d 1 w) n m = 0 := by
  obtain ⟨y, hy⟩ := (memB _).1 hres
  have hc : Continuous fun g : G => (y.1 (e1 (retr N g * (retr N 1)⁻¹)) : M.V) :=
    (show Continuous y.1 from y.2).comp
      (continuous_pi fun _ => (continuous_retr N hN).mul continuous_const)
  have hval : ∀ n : N, retr N (n : G) * (retr N 1)⁻¹ = n := fun n => by
    have := retr_mul N n 1
    rw [mul_one] at this
    rw [this, mul_inv_cancel_right]
  obtain ⟨Y, hYc, hYv⟩ : ∃ Y : G → M.V, Continuous Y ∧ ∀ n : N, Y n = y.1 (e1 n) :=
    ⟨fun g => y.1 (e1 (retr N g * (retr N 1)⁻¹)), hc, fun n => by
      show y.1 (e1 (retr N (n : G) * (retr N 1)⁻¹)) = _
      rw [hval]⟩
  refine ⟨mk1 M Y hYc, fun n hn m hm => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  have h1 := oneDifferential_val (M.resSub N) y ⟨n, hn⟩ ⟨m, hm⟩
  rw [hy] at h1
  have h2 : ((Pair.res M N.subtype continuous_subtype_val).hom.f 2 x).1 ![⟨n, hn⟩, ⟨m, hm⟩] = cur M x n m := by
    refine congrArg x.1 (funext fun i => ?_)
    fin_cases i <;> rfl
  rw [h2] at h1
  rw [h1]
  simp only [D1]
  have e1' : Y n = y.1 (e1 ⟨n, hn⟩) := hYv ⟨n, hn⟩
  have e2' : Y m = y.1 (e1 ⟨m, hm⟩) := hYv ⟨m, hm⟩
  have e3' : Y (n * m) = y.1 (e1 (⟨n, hn⟩ * ⟨m, hm⟩)) := hYv (⟨n, hn⟩ * ⟨m, hm⟩)
  rw [e1', e2', e3']
  exact sub_self _
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
