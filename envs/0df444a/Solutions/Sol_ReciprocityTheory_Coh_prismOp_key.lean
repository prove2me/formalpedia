-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:12:41.201906+00:00
-- url     : https://prove2.me/submissions/9cb4612f-cdcd-4904-8f31-b7d664ea5706

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_P2M_ReciprocityTheory_Coh_hd_succ__7e9ce7f0f9c1
import Theorems.Thm_P2M_ReciprocityTheory_Coh_hd_sub__b0a4dbfa4590
import Theorems.Thm_P2M_ReciprocityTheory_Coh_hd_comp__b3759ba9d99b
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_succ
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_sub
import Theorems.Thm_ReciprocityTheory_Coh_cons_map
import Theorems.Thm_ReciprocityTheory_Coh_map_eq_cons
import Theorems.Thm_ReciprocityTheory_Coh_hd_zero_eval
import Theorems.Thm_ReciprocityTheory_Coh_hd_one_eval
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero_eval
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_one_eval
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
theorem _root_.solution (a b : X → Y) (n : ℕ) : ∀ (F : (Fin (n + 2) → Y) → V) (x : Fin (n + 2) → X),
    hd n (prismOp a b n F) x + prismOp a b (n + 1) (hd (n + 1) F) x =
      F (fun i => b (x i)) - F (fun i => a (x i)) := by
  induction n with
  | zero =>
    intro F x
    rw [hd_zero_eval, prismOp_zero_eval, prismOp_zero_eval, prismOp_one_eval, hd_one_eval, hd_one_eval]
    have eb : (fun i => b (x i)) = ![b (x 0), b (x 1)] := by funext j; fin_cases j <;> rfl
    have ea : (fun i => a (x i)) = ![a (x 0), a (x 1)] := by funext j; fin_cases j <;> rfl
    rw [eb, ea]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    abel
  | succ k ih =>
    intro F x
    let G : (Fin (k + 2) → Y) → V := fun z => F (Fin.cons (a (x 0)) z)
    have sA : hd (k + 1) (prismOp a b (k + 1) F) x = prismOp a b (k + 1) F (Fin.tail x) -
        hd k (fun y => prismOp a b (k + 1) F (Fin.cons (x 0) y)) (Fin.tail x) := hd_succ' _ _ _
    have sBC : hd k (fun y => prismOp a b (k + 1) F (Fin.cons (x 0) y)) (Fin.tail x) =
        hd k (fun z => G (Fin.cons (b (x 0)) z)) (fun j => b (Fin.tail x j)) -
          hd k (prismOp a b k G) (Fin.tail x) := by
      rw [← hd_comp' k (fun z => G (Fin.cons (b (x 0)) z)) b (Fin.tail x), ← hd_sub']
      congr 1; funext y
      rw [prismOp_succ, Fin.cons_zero, Fin.tail_cons, cons_map]
    have sE : prismOp a b (k + 2) (hd (k + 2) F) x = hd (k + 2) F (Fin.cons (a (x 0)) fun j => b (x j)) -
        prismOp a b (k + 1) (fun z => hd (k + 2) F (Fin.cons (a (x 0)) z)) (Fin.tail x) :=
      prismOp_succ _ _ _ _ _
    have hbx : (fun j => b (x j)) = Fin.cons (b (x 0)) fun j => b (Fin.tail x j) := map_eq_cons b x
    have sF1 : hd (k + 2) F (Fin.cons (a (x 0)) fun j => b (x j)) =
        F (fun j => b (x j)) - hd (k + 1) G (fun j => b (x j)) := by
      rw [hd_succ', Fin.cons_zero, Fin.tail_cons]
    have sF2 : hd (k + 1) G (fun j => b (x j)) = G (fun j => b (Fin.tail x j)) -
        hd k (fun z => G (Fin.cons (b (x 0)) z)) (fun j => b (Fin.tail x j)) := by
      rw [hbx, hd_succ', Fin.cons_zero, Fin.tail_cons]
    have sG : (fun z => hd (k + 2) F (Fin.cons (a (x 0)) z)) = fun z => F z - hd (k + 1) G z := by
      funext z; rw [hd_succ', Fin.cons_zero, Fin.tail_cons]
    have hax : F (fun i => a (x i)) = G (fun i => a (Fin.tail x i)) := by
      show F _ = F _; rw [map_eq_cons a x]
    have e : G (fun i => a (Fin.tail x i)) = G (fun i => b (Fin.tail x i)) -
        (hd k (prismOp a b k G) (Fin.tail x) + prismOp a b (k + 1) (hd (k + 1) G) (Fin.tail x)) := by
      rw [ih G (Fin.tail x)]; abel
    rw [sA, sBC, sE, sF1, sF2, sG, prismOp_sub, hax, e]
    abel
end ReciprocityTheory.Coh
