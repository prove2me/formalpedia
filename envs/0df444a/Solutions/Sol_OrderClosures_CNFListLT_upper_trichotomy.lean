-- Prove2me | solution 1 for OrderClosures.CNFListLT.upper_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:07.625096+00:00
-- url     : https://prove2.me/submissions/8eab723e-2391-47d9-8277-dea33b520289

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderClosures_CNFStep_trichotomy
public import Theorems.Thm_OrderClosures_CNFListLT_trans
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
public import Theorems.Thm_OrderConvergesTo_le
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
theorem _root_.solution
    {l m n : List (Ordinal.{u} × Ordinal.{u})}
    (hlm : CNFListLT l m) (hln : CNFListLT l n) :
    m = n ∨ CNFListLT m n ∨ CNFListLT n m := by
  rcases hlm with ⟨p, t, x, y, hl, hm, hxy⟩
  rcases hln with ⟨q, s, x', z, hl', hn, hxz⟩
  have hpref : p <+: l := ⟨x :: t, hl.symm⟩
  have qpref : q <+: l := ⟨x' :: s, hl'.symm⟩
  rcases lt_trichotomy p.length q.length with hpq | hpq | hqp
  · have hprefq : p <+: q := by
      apply (List.isPrefix_append_of_length hpq.le).mp
      rw [hl'] at hpref
      exact hpref
    rcases hprefq with ⟨r, hqr⟩
    rw [← hqr] at hl' hn hxz
    cases r with
    | nil =>
        simp only [List.append_nil] at hqr
        exact (hpq.ne (congrArg List.length hqr)).elim
    | cons w r =>
        have heq : w :: r ++ x' :: s = x :: t :=
          List.append_cancel_left (by
            simpa only [List.cons_append, List.append_assoc] using hl'.symm.trans hl)
        have hw : w = x := (List.cons.inj heq).1
        have hr : r ++ x' :: s = t := (List.cons.inj heq).2
        subst w
        subst t
        refine Or.inr (Or.inr ⟨p, r ++ [z], x, y, ?_, hm, hxy⟩)
        simpa only [List.cons_append, List.append_assoc] using hn
  · have hpqeq : p = q := by
      rw [List.prefix_iff_eq_take] at hpref qpref
      rw [hpref, qpref, hpq]
    subst q
    have heq : x :: t = x' :: s :=
      List.append_cancel_left (hl.symm.trans hl')
    have hxx' : x = x' := (List.cons.inj heq).1
    have hts : t = s := (List.cons.inj heq).2
    subst x'
    subst s
    rcases CNFStep.trichotomy hxy hxz with rfl | hyz | hzy
    · exact Or.inl (hm.trans hn.symm)
    · exact Or.inr (Or.inl ⟨p, [], y, z, hm, hn, hyz⟩)
    · exact Or.inr (Or.inr ⟨p, [], z, y, hn, hm, hzy⟩)
  · have qprefp : q <+: p := by
      apply (List.isPrefix_append_of_length hqp.le).mp
      rw [hl] at qpref
      exact qpref
    rcases qprefp with ⟨r, hpr⟩
    rw [← hpr] at hl hm hxy
    cases r with
    | nil =>
        simp only [List.append_nil] at hpr
        exact (hqp.ne (congrArg List.length hpr)).elim
    | cons w r =>
        have heq : w :: r ++ x :: t = x' :: s :=
          List.append_cancel_left (by
            simpa only [List.cons_append, List.append_assoc] using hl.symm.trans hl')
        have hw : w = x' := (List.cons.inj heq).1
        have hr : r ++ x :: t = s := (List.cons.inj heq).2
        subst w
        subst s
        refine Or.inr (Or.inl ⟨q, r ++ [y], x', z, ?_, hn, hxz⟩)
        simpa only [List.cons_append, List.append_assoc] using hm
end CNFListLT
end OrderClosures
