-- Prove2me | solution 1 for OrderClosures.CNFListLT.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:32.358808+00:00
-- url     : https://prove2.me/submissions/fa496ce6-6c9b-452b-a896-38a48c9342ca

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
public import Theorems.Thm_ClosedOrderIdeal_mem_sInf
public import Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
attribute [local simp] ClosedOrderIdeal.inf_toSubmodule
attribute [local simp] ClosedOrderIdeal.mem_sInf
attribute [local simp] ClosedOrderIdeal.sup_toSubmodule
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom



set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
namespace CNFListLT
theorem _root_.solution {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hmn : CNFListLT m n) : CNFListLT l n := by
  rcases hlm with ⟨p, t, x, y, hl, hm, hxy⟩
  rcases hmn with ⟨q, s, y', z, hm', hn, hyz⟩
  have heq : p ++ [y] = q ++ y' :: s := hm.symm.trans hm'
  have hlen : q.length ≤ p.length := by
    have h : p.length + 1 = q.length + s.length + 1 := by
      simpa only [List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.add_assoc]
        using congrArg List.length heq
    omega
  have hqp : q <+: p := by
    apply (List.isPrefix_append_of_length hlen).mp
    exact ⟨y' :: s, heq.symm⟩
  rcases hqp with ⟨r, hpr⟩
  rw [← hpr] at hl hm hxy heq
  have hr : r ++ [y] = y' :: s :=
    List.append_cancel_left (by simpa only [List.append_assoc] using heq)
  cases r with
  | nil =>
      simp only [List.append_nil] at hl hm hxy
      simp only [List.nil_append] at hr
      simp only [List.cons.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact ⟨q, t, x, z, by simpa only [List.nil_append] using hl,
        hn, CNFStep.trans hxy hyz⟩
  | cons w r =>
      simp only [List.cons_append, List.cons.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      refine ⟨q, r ++ x :: t, w, z, ?_, hn, hyz⟩
      simpa only [List.cons_append, List.append_assoc] using hl
end CNFListLT
end OrderClosures
