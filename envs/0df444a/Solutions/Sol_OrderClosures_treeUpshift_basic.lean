-- Prove2me | solution 1 for OrderClosures.treeUpshift_basic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:47.66513+00:00
-- url     : https://prove2.me/submissions/4c4cc034-6b42-43b3-a57b-716eefd8dd03

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_treeParent_weight_le
public import Theorems.Thm_OrderClosures_treeFunction_le_parent
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
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ) (w : TreeCoefficients n) (hw : 0 ≤ w) :
    treeRho n (treeUpshift n w) ≤ 2 * treeRho n w ∧
      treeOperator n w ≤ treeOperator n (treeUpshift n w) := by
  have hupnonneg : 0 ≤ treeUpshift n w :=
    Finsupp.mapDomain_nonneg hw
  constructor
  · classical
    have hrho_up : treeRho n (treeUpshift n w) =
        (treeUpshift n w).sum fun t a ↦
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * a := by
      rw [treeRho]
      apply Finsupp.sum_congr
      intro t _
      rw [abs_of_nonneg (hupnonneg t)]
    rw [hrho_up]
    rw [treeUpshift, Finsupp.sum_mapDomain_index (by simp) (by simp [mul_add])]
    rw [treeRho, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    rw [abs_of_nonneg (hw t)]
    calc
      (2 : ℝ) ^ (-(TreeNode.level (TreeNode.parent t) : ℤ)) * w t ≤
          (2 * (2 : ℝ) ^ (-(TreeNode.level t : ℤ))) * w t :=
        mul_le_mul_of_nonneg_right (treeParent_weight_le n t) (hw t)
      _ = 2 * ((2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * w t) := by ring
  · classical
    change (w.sum fun t a ↦ a • treeFunction n t) ≤
      (Finsupp.mapDomain TreeNode.parent w).sum fun t a ↦ a • treeFunction n t
    rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    apply Finsupp.sum_le_sum
    intro t _ α
    change w t * treeFunction n t α ≤ w t * treeFunction n (TreeNode.parent t) α
    exact mul_le_mul_of_nonneg_left (treeFunction_le_parent n t α) (hw t)
end OrderClosures
