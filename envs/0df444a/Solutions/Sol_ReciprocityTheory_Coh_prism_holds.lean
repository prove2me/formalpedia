-- Prove2me | solution 1 for ReciprocityTheory.Coh.prism_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:01.753607+00:00
-- url     : https://prove2.me/submissions/f18cef13-09ba-4abc-a105-28688415c200

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero_fun
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_hd_zero
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_key
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_cont
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_equiv
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
open Function
universe u
open Cx
namespace ReciprocityTheory.Coh
theorem _root_.solution : PrismStatement.{u} := by
  intro R _ G _ _ _ M X Y _ _ _ _ A B eA eB hA hB
  refine ⟨fun a ha hga => ?_, fun a b φ ψ ha hb hga hgb hφ hψ n => ?_⟩
  · refine ⟨⟨fun n => (eA n).symm.toLinearMap ∘ₗ pullH M a ha hga n ∘ₗ (eB n).toLinearMap, ?_⟩, ?_⟩
    · intro n F
      apply (eA (n + 1)).injective
      apply Subtype.ext
      funext x
      show (eA (n + 1) ((eA (n + 1)).symm (pullH M a ha hga (n + 1) (eB (n + 1) (B.d n F))))).1 x =
        (eA (n + 1) (A.d n ((eA n).symm (pullH M a ha hga n (eB n F))))).1 x
      rw [LinearEquiv.apply_symm_apply, hA, LinearEquiv.apply_symm_apply]
      show (eB (n + 1) (B.d n F)).1 (fun i => a (x i)) = hd n (fun y => (eB n F).1 fun i => a (y i)) x
      rw [hB]; rfl
    · intro n F x
      show (eA n ((eA n).symm (pullH M a ha hga n (eB n F)))).1 x = _
      rw [LinearEquiv.apply_symm_apply]; rfl
  · apply Submodule.linearMap_qext
    apply LinearMap.ext
    rintro ⟨F, hF⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Hom.H, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    show φ.f n F - ψ.f n F ∈ A.B n
    have hF0 : B.d n F = 0 := hF
    have hF' : hd n (eB n F).1 = 0 := by
      have h1 := hB n F
      rw [hF0, map_zero] at h1
      exact h1.symm
    cases n with
    | zero =>
      have h : φ.f 0 F = ψ.f 0 F := by
        apply (eA 0).injective; apply Subtype.ext; funext x
        rw [hφ, hψ]
        have h2 := prismOp_hd_zero a b (eB 0 F).1 x
        rw [hF'] at h2
        have h0 : prismOp a b 0 (0 : (Fin 2 → Y) → M.V) x = 0 := rfl
        exact (sub_eq_zero.mp (h2.symm.trans h0)).symm
      rw [h, sub_self]; exact Submodule.zero_mem _
    | succ n =>
      let F' := (eB (n + 1) F).1
      have hc : Continuous F' := (eB (n + 1) F).2.1
      let H : hcoch M X n := ⟨prismOp a b n F',
        prismOp_cont a b ha hb n (fun _ => F') (hc.comp continuous_snd) id continuous_id,
        fun g x => prismOp_equiv a b hga hgb g (M.rho g).toAddMonoidHom n F' F'
          (fun y => (eB (n + 1) F).2.2 g y) x⟩
      have hdH : A.d n ((eA n).symm H) = ψ.f (n + 1) F - φ.f (n + 1) F := by
        apply (eA (n + 1)).injective; apply Subtype.ext; funext x
        rw [hA, LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub, Pi.sub_apply, hφ, hψ]
        have h2 := prismOp_key a b n F' x
        have h0 : prismOp a b (n + 1) (0 : (Fin (n + 3) → Y) → M.V) x = 0 := prismOp_zero_fun a b (n + 1) x
        rw [hF', h0, add_zero] at h2
        exact h2
      show φ.f (n + 1) F - ψ.f (n + 1) F ∈ LinearMap.range (A.d n)
      exact ⟨-(eA n).symm H, by rw [map_neg, hdH, neg_sub]⟩
end ReciprocityTheory.Coh
