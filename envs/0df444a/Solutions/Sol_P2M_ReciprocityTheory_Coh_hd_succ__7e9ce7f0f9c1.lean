-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_hd_succ__7e9ce7f0f9c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:56.454163+00:00
-- url     : https://prove2.me/submissions/03188c98-77d5-4dd1-8a91-4ac49d868190

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
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
theorem _root_.solution (n : ℕ) (F : (Fin (n + 2) → X) → V) (x : Fin (n + 3) → X) :
    hd (n + 1) F x = F (Fin.tail x) - hd n (fun y => F (Fin.cons (x 0) y)) (Fin.tail x) := by
  unfold hd
  rw [Fin.sum_univ_succ]
  have h0 : ((-1 : ℤ) ^ ((0 : Fin (n + 3)) : ℕ) • F fun j => x (Fin.succAbove 0 j)) = F (Fin.tail x) := by
    rw [Fin.val_zero, pow_zero, one_smul]; rfl
  have h1 : ∀ i : Fin (n + 2), ((-1 : ℤ) ^ (i.succ : ℕ) • F fun j => x (i.succ.succAbove j)) =
      -((-1 : ℤ) ^ (i : ℕ) • F (Fin.cons (x 0) fun j => Fin.tail x (i.succAbove j))) := by
    intro i
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
    congr 3
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.succ_succAbove_succ, Fin.tail]
  rw [h0, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_neg_distrib, sub_eq_add_neg]
end ReciprocityTheory.Coh
