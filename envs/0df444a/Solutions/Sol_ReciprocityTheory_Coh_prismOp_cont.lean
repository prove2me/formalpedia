-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:34.3023+00:00
-- url     : https://prove2.me/submissions/381cf80c-e74b-407b-914a-86bcd75018d9

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_succ
import Theorems.Thm_P2M_ReciprocityTheory_Coh_cont_cons__f1a3f8bb1a53
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
theorem _root_.solution [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (a b : X → Y) (ha : Continuous a) (hb : Continuous b) (n : ℕ) :
    ∀ {S : Type u} [TopologicalSpace S] (Φ : S → (Fin (n + 2) → Y) → V),
      Continuous (fun p : S × (Fin (n + 2) → Y) => Φ p.1 p.2) →
      ∀ v : S → Fin (n + 1) → X, Continuous v → Continuous fun s => prismOp a b n (Φ s) (v s) := by
  induction n with
  | zero =>
    intro S _ Φ hΦ v hv
    simp only [prismOp_zero]
    refine hΦ.comp (continuous_id.prodMk ?_)
    exact cont_cons' _ (fun s j => b (v s j)) (ha.comp ((continuous_apply 0).comp hv))
      (continuous_pi fun j => hb.comp ((continuous_apply j).comp hv))
  | succ k ih =>
    intro S _ Φ hΦ v hv
    simp only [prismOp_succ]
    refine Continuous.sub ?_ ?_
    · refine hΦ.comp (continuous_id.prodMk ?_)
      exact cont_cons' _ (fun s j => b (v s j)) (ha.comp ((continuous_apply 0).comp hv))
        (continuous_pi fun j => hb.comp ((continuous_apply j).comp hv))
    · refine ih (fun s y => Φ s (Fin.cons (a (v s 0)) y)) ?_ (fun s => Fin.tail (v s))
        (continuous_pi fun j => (continuous_apply _).comp hv)
      refine hΦ.comp (continuous_fst.prodMk ?_)
      exact cont_cons' (fun p : S × (Fin (k + 2) → Y) => a (v p.1 0)) (fun p => p.2)
        (ha.comp ((continuous_apply 0).comp (hv.comp continuous_fst))) continuous_snd
end ReciprocityTheory.Coh
