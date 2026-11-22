-- Prove2me | solution 1 for OrderClosures.one_le_dist_booleanStoneIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:21.932915+00:00
-- url     : https://prove2.me/submissions/3fd9a824-da34-4df4-ba26-29fb5dbbb1a0

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
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
open Set
noncomputable section
open OrderClosures
universe u v
namespace OrderClosures
theorem _root_.solution
    (B : Type u) [CompleteBooleanAlgebra B] {a b : B} (hab : a ≠ b) :
    (1 : ℝ) ≤ dist (booleanStoneIndicator B a) (booleanStoneIndicator B b) := by
  rw [dist_eq_norm]
  by_cases hle : a ≤ b
  · have hnle : ¬ b ≤ a := fun hba ↦ hab (le_antisymm hle hba)
    rcases exists_booleanStonePoint_of_not_le B hnle with ⟨x, hxb, hxa⟩
    calc
      (1 : ℝ) = ‖(booleanStoneIndicator B a - booleanStoneIndicator B b) x‖ := by
        simp [booleanStoneIndicator_apply, hxa, hxb]
      _ ≤ ‖booleanStoneIndicator B a - booleanStoneIndicator B b‖ :=
        ContinuousMap.norm_coe_le_norm _ _
  · rcases exists_booleanStonePoint_of_not_le B hle with ⟨x, hxa, hxb⟩
    calc
      (1 : ℝ) = ‖(booleanStoneIndicator B a - booleanStoneIndicator B b) x‖ := by
        simp [booleanStoneIndicator_apply, hxa, hxb]
      _ ≤ ‖booleanStoneIndicator B a - booleanStoneIndicator B b‖ :=
        ContinuousMap.norm_coe_le_norm _ _
end OrderClosures
