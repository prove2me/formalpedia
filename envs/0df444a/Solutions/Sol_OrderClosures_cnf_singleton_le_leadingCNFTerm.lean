-- Prove2me | solution 1 for OrderClosures.cnf_singleton_le_leadingCNFTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:30.163867+00:00
-- url     : https://prove2.me/submissions/64203649-11b9-46d2-836a-27322a639a02

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
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
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
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
theorem _root_.solution
    {q a γ d : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)]) (hqa : q ≤ a) :
    q ≤ leadingCNFTerm a := by
  have hqeq : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Ordinal.CNF.zero_right] at hq
    simp at hq
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  have hlogq : Ordinal.log Ordinal.omega0 q = γ := by
    rw [hqeq, Ordinal.log_opow_mul Ordinal.one_lt_omega0 γ hdpos.ne',
      Ordinal.log_eq_zero hdlt, add_zero]
  have ha0 : a ≠ 0 := by
    intro ha
    apply hq0
    exact le_antisymm (ha ▸ hqa) (zero_le : (0 : Ordinal) ≤ q)
  have hlogle := Ordinal.log_mono_right Ordinal.omega0 hqa
  rw [hlogq] at hlogle
  rcases hlogle.eq_or_lt with hloge | hloglt
  · rw [leadingCNFTerm, ← hloge, hqeq]
    apply mul_le_mul_right
    exact (Ordinal.mul_le_iff_le_div
      (Ordinal.opow_ne_zero γ Ordinal.omega0_ne_zero)).mp (hqeq ▸ hqa)
  · have hqpow : q < Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hq0).2 (by
        simpa only [hlogq] using hloglt)
    exact hqpow.le.trans (by
      rw [leadingCNFTerm]
      exact Ordinal.le_mul_left _
        (Ordinal.div_opow_log_pos Ordinal.omega0 ha0))
end OrderClosures
