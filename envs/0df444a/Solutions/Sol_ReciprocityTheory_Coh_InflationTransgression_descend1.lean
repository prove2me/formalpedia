-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.descend1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:33.539118+00:00
-- url     : https://prove2.me/submissions/1b54bd11-9bd7-4227-baf0-a9905b88477a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB
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
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution (w : G → M.V) (hw : Continuous w) (hr : ∀ a (n : N), w (a * n) = w a)
    (hi : ∀ a (n : N), M.rho n (w a) = w a) :
    ∃ v : Q.coch.X 1, ∀ a : G, P.u (v.1 (e1 (a : G ⧸ N))) = w a := by
  letI : Setoid G := QuotientGroup.leftRel N
  have hw' : ∀ a b : G, a ≈ b → w a = w b := by
    intro a b hab
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
    have e := hr a ⟨a⁻¹ * b, hab'⟩
    simp only [mul_inv_cancel_left] at e
    exact e.symm
  let wq : G ⧸ N → M.V := Quotient.lift w hw'
  have hwq : Continuous wq := hw.quotient_lift hw'
  have hmem : ∀ x : G ⧸ N, wq x ∈ LinearMap.range P.u := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a => exact (hP.2.2 (w a)).2 fun g hg => hi a ⟨g, hg⟩
  let v0 : G ⧸ N → Q.V := fun x => (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨wq x, hmem x⟩
  have hv0u : ∀ x, P.u (v0 x) = wq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨wq x, hmem x⟩
    exact congrArg Subtype.val this
  have hv0 : Continuous v0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ v0) = wq := funext hv0u
    rw [e]
    exact hwq
  refine ⟨⟨fun g => v0 (g 0), hv0.comp (continuous_apply 0)⟩, fun a => ?_⟩
  exact hv0u _
end ReciprocityTheory.Coh.InflationTransgression
