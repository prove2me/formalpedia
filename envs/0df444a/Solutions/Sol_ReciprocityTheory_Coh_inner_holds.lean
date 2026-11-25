-- Prove2me | solution 1 for ReciprocityTheory.Coh.inner_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:41:06.724596+00:00
-- url     : https://prove2.me/submissions/6f35d8cd-30f0-49a3-8c96-ab1ddc024ff0

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
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
import Theorems.Thm_ReciprocityTheory_Coh_homogIso_holds
import Theorems.Thm_ReciprocityTheory_Coh_prism_holds
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
open ReciprocityTheory.Gal Cx
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : InnerStatement.{u} := by
  intro R _ G _ _ _ M P s hφ hu n
  obtain ⟨e, he, he1, -⟩ := homogIso_holds R G M
  have hcomp : ∀ (n : ℕ) (F : M.coch.X n) (x : Fin (n + 1) → G),
      (e n (P.hom.f n F)).1 x = (e n F).1 fun i => x i * s := by
    intro n F x
    rw [he1, he1]
    show M.rho (x 0) (P.u (F.1 fun i => P.φ ((x i.castSucc)⁻¹ * x i.succ))) =
      M.rho (x 0 * s) (F.1 fun i => (x i.castSucc * s)⁻¹ * (x i.succ * s))
    rw [hu, map_mul]
    first
    | rw [LinearMap.mul_apply]
    | rw [Module.End.mul_apply]
    congr 1
    congr 1
    exact congrArg F.1 (funext fun i => by rw [hφ]; group)
  have key := (prism_holds R G M G G M.coch M.coch e e he he).2 (fun x => x * s) id P.hom
    (Cx.Hom.id M.coch) (continuous_id.mul continuous_const) continuous_id
    (fun g x => by simp only [smul_eq_mul, mul_assoc]) (fun g x => rfl) hcomp
    (fun n F x => rfl) n
  rw [key, Cx.Hom.id_H]
end ReciprocityTheory.Coh
