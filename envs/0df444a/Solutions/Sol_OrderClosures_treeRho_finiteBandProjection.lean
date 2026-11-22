-- Prove2me | solution 1 for OrderClosures.treeRho_finiteBandProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:31.967802+00:00
-- url     : https://prove2.me/submissions/13e1ee55-a4e5-47a6-ba65-d1c58ce91339

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_node_mem_its_treeBand
public import Theorems.Thm_OrderClosures_treeBandOfNode_eq_of_mem
public import Theorems.Thm_OrderClosures_finiteBandProjection_apply
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
theorem _root_.solution (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    treeRho n (finiteBandProjection n Λ w) =
      ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) := by
  classical
  have hfinite : treeRho n (finiteBandProjection n Λ w) =
      ∑ t ∈ w.support, (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) *
        |finiteBandProjection n Λ w t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset
    · rw [finiteBandProjection, Finsupp.support_filter]
      exact Finset.filter_subset _ _
    · simp
  have hband (B : TreeBandIndex n) : treeRho n (treeBandProjection n B w) =
      ∑ t ∈ w.support, (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) *
        |treeBandProjection n B w t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset
    · rw [treeBandProjection, Finsupp.support_filter]
      exact Finset.filter_subset _ _
    · simp
  rw [hfinite]
  simp_rw [hband]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hΛ : treeBandOfNode n t ∈ Λ
  · rw [(finiteBandProjection_apply n Λ w t).1 hΛ]
    rw [Finset.sum_eq_single (treeBandOfNode n t)]
    · rw [treeBandProjection, Finsupp.filter_apply_pos]
      exact node_mem_its_treeBand n t
    · intro B hBΛ hBne
      have hnot : t ∉ treeBandSupport n B := by
        intro htB
        exact hBne (treeBandOfNode_eq_of_mem n t B htB).symm
      rw [treeBandProjection, Finsupp.filter_apply_neg _ _ hnot]
      simp
    · intro hnot
      exact (hnot hΛ).elim
  · rw [(finiteBandProjection_apply n Λ w t).2 hΛ]
    simp only [abs_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro B hBΛ
    have hnot : t ∉ treeBandSupport n B := by
      intro htB
      exact hΛ (treeBandOfNode_eq_of_mem n t B htB ▸ hBΛ)
    rw [treeBandProjection, Finsupp.filter_apply_neg _ _ hnot]
    simp
end OrderClosures
