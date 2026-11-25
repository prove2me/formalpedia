-- Prove2me | solution 1 for ReciprocityTheory.Coh.HomogeneousCochainIso.eFun_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:45:55.820705+00:00
-- url     : https://prove2.me/submissions/2dbf8228-e783-4378-996d-1f6bcc4d710f

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
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
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.HomogeneousCochainIso
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.HomogeneousCochainIso
theorem _root_.solution (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 2) → G)
    (j : Fin (n + 1)) :
    eFun M n f (fun k => x (j.succ.succAbove k)) =
      M.rho (x 0) (f (Fin.contractNth j (· * ·) fun i => (x i.castSucc)⁻¹ * x i.succ)) := by
  have key : (fun i : Fin n => (x (j.succ.succAbove i.castSucc))⁻¹ * x (j.succ.succAbove i.succ)) =
      Fin.contractNth j (· * ·) fun i => (x i.castSucc)⁻¹ * x i.succ := by
    have hp : ∀ c, Fin.partialProd (fun i => (x i.castSucc)⁻¹ * x i.succ) c = (x 0)⁻¹ * x c := by
      intro c
      have h := congrFun (Fin.partialProd_left_inv x) c
      simp only [Pi.smul_apply, smul_eq_mul] at h
      exact eq_inv_mul_of_mul_eq h
    funext k
    rw [← Fin.inv_partialProd_mul_eq_contractNth, ← Fin.succ_succAbove_succ, hp, hp]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  simp only [eFun, Fin.succ_succAbove_zero]
  rw [key]
end ReciprocityTheory.Coh.HomogeneousCochainIso
