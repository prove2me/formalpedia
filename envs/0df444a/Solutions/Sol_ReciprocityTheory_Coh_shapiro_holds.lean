-- Prove2me | solution 1 for ReciprocityTheory.Coh.shapiro_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:02.27125+00:00
-- url     : https://prove2.me/submissions/2a76a234-a4b5-4d8b-96c4-5349f0587c6c

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Theorems.Thm_ReciprocityTheory_Coh_shp_hom_ext
import Theorems.Thm_ReciprocityTheory_Coh_shp_bij_of_inv
import Theorems.Thm_ReciprocityTheory_Coh_shp_qi_of_bij
import Theorems.Thm_ReciprocityTheory_Coh_shpPush_apply
import Theorems.Thm_ReciprocityTheory_Coh_shpPush_hd
import Theorems.Thm_ReciprocityTheory_Coh_shpPush_bij
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
import Theorems.Thm_ReciprocityTheory_Coh_homogExists_holds
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
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : ShapiroStatement.{u} := by
  intro R _ G _ _ _ _ U M C ev hev hr'
  obtain ⟨hφ, j, hj, hjc, hrj⟩ := hev
  obtain ⟨r, hrc, hrx⟩ := hr'
  obtain ⟨eC, hC, hCf, -⟩ := homogIso_holds R G C
  obtain ⟨eM, hM, hMf, -⟩ := homogIso_holds R U M
  obtain ⟨B, eB, hB⟩ := homogExists_holds R U M G
  obtain ⟨P, hP⟩ : ∃ P : Hom C.coch B, ∀ n f, eB n (P.f n f) = shpPush ev hφ n (eC n f) :=
    ⟨⟨fun n => ((eB n).symm.toLinearMap.comp (shpPush ev hφ n)).comp (eC n).toLinearMap, fun n F => by
      apply (eB (n + 1)).injective
      apply Subtype.ext
      rw [hB]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact shpPush_hd ev hφ n _ _ (hC n F)⟩,
     fun n f => (eB n).apply_symm_apply _⟩
  obtain ⟨φ1, hφ1⟩ := (prism_holds R U M U G M.coch B eM eB hM hB).1 Subtype.val
    continuous_subtype_val (fun g x => rfl)
  obtain ⟨φ2, hφ2⟩ := (prism_holds R U M G U B M.coch eB eM hB hM).1 r hrc (fun g x => hrx g x)
  have h12 : ∀ n, (φ1.comp φ2).H n = (Hom.id M.coch).H n :=
    (prism_holds R U M U U M.coch M.coch eM eM hM hM).2 (fun u => r u) id (φ1.comp φ2) (Hom.id _)
      (hrc.comp continuous_subtype_val) continuous_id (fun g x => hrx g x) (fun g x => rfl)
      (fun n F x => by
        show (eM n (φ1.f n (φ2.f n F))).1 x = _
        rw [hφ1, hφ2])
      (fun n F x => rfl)
  have h21 : ∀ n, (φ2.comp φ1).H n = (Hom.id B).H n :=
    (prism_holds R U M G G B B eB eB hB hB).2 (fun g => (r g : G)) id (φ2.comp φ1) (Hom.id _)
      (continuous_subtype_val.comp hrc) continuous_id
      (fun g x => by
        show ((r (↑g * x) : U) : G) = ↑g * ↑(r x)
        rw [hrx, Subgroup.coe_mul])
      (fun g x => rfl)
      (fun n F x => by
        show (eB n (φ2.f n (φ1.f n F))).1 x = _
        rw [hφ2, hφ1])
      (fun n F x => rfl)
  have hPb : ∀ n, Bijective (P.f n) := fun n => by
    have hfun : ⇑(P.f n) = (eB n).symm ∘ (shpPush ev hφ n) ∘ (eC n) := by
      funext f
      simp only [Function.comp_apply]
      rw [← hP, LinearEquiv.symm_apply_apply]
    rw [hfun]
    exact (eB n).symm.bijective.comp
      ((shpPush_bij (ev := ev) (hφ := hφ) (j := j) (hj := hj) (hjc := hjc) (hr := hrj) n).comp
        (eC n).bijective)
  have hL : ∀ n f x, (eM n (ev.hom.f n f)).1 x =
      ev.u (C.rho (x 0 : G) (f.1 fun i => ((x i.castSucc : G))⁻¹ * x i.succ)) := by
    intro n f x
    rw [hMf]
    show M.rho (x 0) (ev.u (f.1 fun i => ev.φ ((x i.castSucc)⁻¹ * x i.succ))) = _
    rw [← ev.equiv]
    simp only [shp_phi ev hφ, Subgroup.coe_mul, Subgroup.coe_inv]
  have hR : ∀ n f x, (eM n ((φ1.comp P).f n f)).1 x =
      ev.u (C.rho (x 0 : G) (f.1 fun i => ((x i.castSucc : G))⁻¹ * x i.succ)) := by
    intro n f x
    show (eM n (φ1.f n (P.f n f))).1 x = _
    rw [hφ1, hP, shpPush_apply, hCf]
  have hev : ev.hom = φ1.comp P := shp_hom_ext fun n => LinearMap.ext fun f =>
    (eM n).injective (Subtype.ext (funext fun x => (hL n f x).trans (hR n f x).symm))
  intro n
  rw [hev]
  have hc : ∀ y, (φ1.comp P).H n y = φ1.H n (P.H n y) := fun y => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  have hfun : ⇑((φ1.comp P).H n) = φ1.H n ∘ P.H n := funext hc
  rw [hfun]
  exact (shp_bij_of_inv φ1 φ2 n (h21 n) (h12 n)).comp (shp_qi_of_bij P hPb n)
end ReciprocityTheory.Coh
