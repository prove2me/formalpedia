-- Prove2me | solution 1 for OrderClosures.tree_sharp_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:04.492262+00:00
-- url     : https://prove2.me/submissions/cc62c018-273a-432b-8cac-037e7efe6d9f

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_treeRho_bandProjection_le
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
theorem _root_.solution
    (n : ℕ) (w : ℕ → TreeCoefficients n) (C : ℝ)
    (hw : ∀ m, treeRho n (w m) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B : TreeBandIndex n,
      ∃ l : ℝ, Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w (φ m))))
        atTop (nhds l) := by
  classical
  let : Countable (TreeNode n) := by
    unfold TreeNode
    infer_instance
  let : Countable (TreeNonterminal n) := by
    unfold TreeNonterminal
    infer_instance
  let D := max C 0
  let y : ℕ → TreeBandIndex n → Set.Icc (0 : ℝ) D := fun m B ↦
    ⟨treeRho n (treeBandProjection n B (w m)),
      treeRho_nonneg n _,
      (treeRho_bandProjection_le n B (w m)).trans
        ((hw m).trans (le_max_left C 0))⟩
  let : SeqCompactSpace (TreeBandIndex n → Set.Icc (0 : ℝ) D) := inferInstance
  obtain ⟨l, _, φ, hφ, hlim⟩ :=
    (SeqCompactSpace.isSeqCompact_univ
      (X := TreeBandIndex n → Set.Icc (0 : ℝ) D)) (x := y) (fun _ ↦ Set.mem_univ _)
  refine ⟨φ, hφ, fun B ↦ ⟨(l B).1, ?_⟩⟩
  have hcoord := tendsto_pi_nhds.mp hlim B
  simpa [y, Function.comp_def] using tendsto_subtype_rng.mp hcoord
end OrderClosures
