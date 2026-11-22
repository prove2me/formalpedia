-- Prove2me | solution 1 for OrderClosures.singletonCNFBelow_isLUB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:47.884797+00:00
-- url     : https://prove2.me/submissions/cda7bf12-38c5-4220-9f2a-372630b7c953

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
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
theorem _root_.solution (γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    IsLUB (singletonCNFBelow γ) (Ordinal.omega0 ^ γ) := by
  constructor
  · rintro q ⟨δ, d, hq, hqpow⟩
    exact hqpow.le
  · intro c hc
    have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ γ) :=
      Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hγ
    apply hlim.isLUB_Iio.2
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      exact zero_le
    let δ := Ordinal.log Ordinal.omega0 r
    let d := r / Ordinal.omega0 ^ δ
    let q := Ordinal.omega0 ^ δ * (d + 1)
    have hdpos : 0 < d := Ordinal.div_opow_log_pos Ordinal.omega0 hr0
    have hdlt : d < Ordinal.omega0 :=
      Ordinal.div_opow_log_lt r Ordinal.one_lt_omega0
    have hdsuccpos : 0 < d + 1 := hdpos.trans_le le_self_add
    have hdsucclt : d + 1 < Ordinal.omega0 := by
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hdlt
      rw [hn, ← Nat.cast_one, ← Nat.cast_add]
      exact Ordinal.natCast_lt_omega0 (n + 1)
    have hδγ : δ < γ :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hr0).mp hr
    have hqcnf : Ordinal.CNF Ordinal.omega0 q = [(δ, d + 1)] := by
      dsimp [q]
      simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
        (e := δ) (x := d + 1) (y := 0) Ordinal.one_lt_omega0
        hdsuccpos.ne' hdsucclt (Ordinal.opow_pos δ Ordinal.omega0_pos)
    have hqpow : q < Ordinal.omega0 ^ γ := by
      dsimp [q]
      simpa only [add_zero] using Ordinal.opow_mul_add_lt_opow hdsucclt
        (Ordinal.opow_pos δ Ordinal.omega0_pos) hδγ
    have hrq : r < q := by
      rw [← Ordinal.div_add_mod r (Ordinal.omega0 ^ δ)]
      dsimp [q, d]
      exact Ordinal.opow_mul_add_lt_opow_mul
        (Ordinal.mod_lt r (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero))
        (lt_add_one (r / Ordinal.omega0 ^ δ))
    exact hrq.le.trans (hc ⟨δ, d + 1, hqcnf, hqpow⟩)
end OrderClosures
