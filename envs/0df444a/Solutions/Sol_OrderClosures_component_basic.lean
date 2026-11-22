-- Prove2me | solution 1 for OrderClosures.component_basic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:58.232798+00:00
-- url     : https://prove2.me/submissions/3b36a257-3427-40a9-a377-8ff23c9f70f8

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Theorems.Thm_OrderClosures_treeSeminorm_exact_basis
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
public import Theorems.Thm_VectorSublattice_separableSpace_topologicalClosure_generated_of_countable
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
theorem _root_.solution (n : ℕ) :
    TopologicalSpace.IsSeparable (Set.univ : Set (TreeComponent n)) ∧
      IsCompleteFor (componentLatticeNorm n) ∧
      componentLatticeNorm n (componentRoot n) = 1 ∧
      (∀ t : TreeNode n, TreeNode.level t = n →
        componentLatticeNorm n (componentTreeFunction n t) =
          (2 : ℝ) ^ (-(n : ℤ))) := by
  have hseparable : TopologicalSpace.IsSeparable
      (Set.univ : Set (TreeComponent n)) := by
    let : Countable (TreeNode n) := by
      unfold TreeNode
      infer_instance
    let : TopologicalSpace.SeparableSpace (TreeComponent n) :=
      VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
        (Set.countable_range (treeFunction n))
    exact TopologicalSpace.isSeparable_univ_iff.mpr inferInstance
  have hcomplete : IsCompleteFor (componentLatticeNorm n) := by
    intro f hf
    have hnormCauchy : CauchySeq (fun m ↦ (f m).1) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
      obtain ⟨N, hN⟩ := hf (ε / (2 : ℝ) ^ n) (div_pos hε hpow)
      refine ⟨N, fun m hm k hk ↦ ?_⟩
      have hp := hN m hm k hk
      have hnorm := (treeSeminorm_norm_comparison n ((f m).1 - (f k).1)).2
      rw [dist_eq_norm_sub]
      change treeSeminorm n ((f m).1 - (f k).1) < ε / (2 : ℝ) ^ n at hp
      have hscaled := mul_lt_mul_of_pos_left hp hpow
      rw [mul_div_cancel₀ _ hpow.ne'] at hscaled
      exact hnorm.trans_lt hscaled
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hnormCauchy
    have hymem : y ∈ treeSublattice n := by
      apply isClosed_closure.mem_of_tendsto hy
      exact Eventually.of_forall fun m ↦ (f m).2
    let z : TreeComponent n := ⟨y, hymem⟩
    refine ⟨z, ?_⟩
    rw [Metric.tendsto_atTop] at hy
    intro ε hε
    obtain ⟨N, hN⟩ := hy ε hε
    refine ⟨N, fun m hm ↦ ?_⟩
    have hp := (treeSeminorm_norm_comparison n ((f m).1 - y)).1
    have hdist := hN m hm
    rw [dist_eq_norm_sub] at hdist
    change treeSeminorm n ((f m).1 - y) < ε
    exact hp.trans_lt hdist
  refine ⟨hseparable, hcomplete, ?_, ?_⟩
  · change treeSeminorm n (treeFunction n (TreeNode.root n)) = 1
    simpa [TreeNode.root, TreeNode.level] using
      (treeSeminorm_exact_basis n (TreeNode.root n)).2
  · intro t ht
    change treeSeminorm n (treeFunction n t) = (2 : ℝ) ^ (-(n : ℤ))
    simpa [ht] using (treeSeminorm_exact_basis n t).2
end OrderClosures
