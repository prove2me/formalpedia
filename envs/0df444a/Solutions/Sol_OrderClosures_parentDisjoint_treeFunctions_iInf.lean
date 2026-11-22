-- Prove2me | solution 1 for OrderClosures.parentDisjoint_treeFunctions_iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:17.873824+00:00
-- url     : https://prove2.me/submissions/7c8b1d9b-de2a-4527-bbaa-a2258ee90f2a

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Theorems.Thm_OrderClosures_finiteTreeSup_nonneg
public import Theorems.Thm_OrderClosures_finiteTreeSup_apply_of_notMem
public import Theorems.Thm_OrderClosures_commonLower_le_zero_of_parentDisjoint_subseq
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
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n)) (F j : Set (TreeNode n))) :
    IsGLB (Set.range fun m ↦ finiteTreeSup n (F m)) 0 := by
  constructor
  · rintro _ ⟨m, rfl⟩
    exact finiteTreeSup_nonneg n (F m)
  · intro z hz
    have hzall : ∀ m, z ≤ finiteTreeSup n (F m) := fun m ↦ hz ⟨m, rfl⟩
    by_cases hrootExists : ∃ i, TreeNode.root n ∈ F i
    · obtain ⟨i, hi⟩ := hrootExists
      let φ : ℕ → ℕ := fun m ↦ i + m + 1
      have hφ : Function.Injective φ := by
        intro a b h
        dsimp [φ] at h
        omega
      have hroot : ∀ m, TreeNode.root n ∉ F (φ m) := by
        intro m hm
        have hne : i ≠ φ m := by
          dsimp [φ]
          omega
        have hdis := hF hne
        have hmem : TreeNode.root n ∈
            TreeNode.parent '' (F i : Set (TreeNode n)) ∩
              TreeNode.parent '' (F (φ m) : Set (TreeNode n)) := by
          constructor
          · exact ⟨TreeNode.root n, hi, by rfl⟩
          · exact ⟨TreeNode.root n, hm, by rfl⟩
        rw [hdis] at hmem
        exact hmem
      exact commonLower_le_zero_of_parentDisjoint_subseq n F hF φ hφ hroot
        (fun m ↦ finiteTreeSup n (F m))
        (fun m α hα ↦ finiteTreeSup_apply_of_notMem n _ hα) hzall
    · push Not at hrootExists
      exact commonLower_le_zero_of_parentDisjoint_subseq n F hF id
        Function.injective_id hrootExists (fun m ↦ finiteTreeSup n (F m))
        (fun m α hα ↦ finiteTreeSup_apply_of_notMem n _ hα) hzall
end OrderClosures
