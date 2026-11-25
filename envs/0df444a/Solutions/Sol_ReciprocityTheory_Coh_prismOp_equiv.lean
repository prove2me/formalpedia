-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:02.273982+00:00
-- url     : https://prove2.me/submissions/5c94a656-3f41-4a99-a62d-1821c6787aa7

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_succ
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
variable {V X Y : Type u} [AddCommGroup V]
namespace ReciprocityTheory.Coh
theorem _root_.solution {G : Type u} [SMul G X] [SMul G Y] (a b : X → Y)
    (ha : ∀ (g : G) x, a (g • x) = g • a x) (hb : ∀ (g : G) x, b (g • x) = g • b x)
    (g : G) (ρ : V →+ V) (n : ℕ) : ∀ (F F' : (Fin (n + 2) → Y) → V),
      (∀ y, F (fun i => g • y i) = ρ (F' y)) →
      ∀ x, prismOp a b n F (fun i => g • x i) = ρ (prismOp a b n F' x) := by
  have hc : ∀ {m : ℕ} (y0 : Y) (y : Fin m → Y),
      (Fin.cons (g • y0) fun j => g • y j : Fin (m + 1) → Y) = fun i => g • (Fin.cons y0 y : Fin (m + 1) → Y) i := by
    intro m y0 y; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  induction n with
  | zero =>
    intro F F' hF x
    simp only [prismOp_zero, ha, hb]
    rw [hc, hF]
  | succ k ih =>
    intro F F' hF x
    rw [prismOp_succ, prismOp_succ, map_sub]
    congr 1
    · simp only [ha, hb]; rw [hc, hF]
    · refine ih _ _ (fun y => ?_) (Fin.tail x)
      simp only [ha]; rw [hc, hF]
end ReciprocityTheory.Coh
