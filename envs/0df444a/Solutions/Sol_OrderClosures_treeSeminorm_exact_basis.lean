-- Prove2me | solution 1 for OrderClosures.treeSeminorm_exact_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:25.542796+00:00
-- url     : https://prove2.me/submissions/a21d2d7b-84be-4e3b-945e-22f79ef951a3

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Theorems.Thm_OrderClosures_treeOperator_apply
public import Theorems.Thm_OrderClosures_level_le_of_treeCylinder_subset
public import Theorems.Thm_OrderClosures_treeFunction_nonneg
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
public import Theorems.Thm_OrderClosures_treeCylinder_finite_cover
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_mem
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_notMem
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
theorem _root_.solution (n : ℕ) (t : TreeNode n) :
    (∀ w : TreeCoefficients n, 0 ≤ w → treeFunction n t ≤ treeOperator n w →
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) ≤ treeRho n w) ∧
    treeSeminorm n (treeFunction n t) =
      (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) := by
  classical
  let a : ℝ := (2 : ℝ) ^ (-(TreeNode.level t : ℤ))
  have ha : 0 < a := zpow_pos (by norm_num) _
  have hlower : ∀ w : TreeCoefficients n, 0 ≤ w →
      treeFunction n t ≤ treeOperator n w → a ≤ treeRho n w := by
    intro w hw hdom
    let C := w.support.filter fun u ↦ treeCylinder n t ⊆ treeCylinder n u
    let N := w.support.filter fun u ↦ ¬treeCylinder n t ⊆ treeCylinder n u
    have hnotcover : ¬(∀ α ∈ treeCylinder n t,
        ∃ u ∈ N, α ∈ treeCylinder n u) := by
      intro hcover
      obtain ⟨u, huN, hsub⟩ := treeCylinder_finite_cover n t N hcover
      exact (Finset.mem_filter.mp huN).2 hsub
    push Not at hnotcover
    obtain ⟨α, hαt, hαN⟩ := hnotcover
    have hoperator : treeOperator n w α = ∑ u ∈ C, w u := by
      rw [treeOperator_apply, Finsupp.sum]
      change (∑ u ∈ w.support, w u * treeFunction n u α) = ∑ u ∈ C, w u
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hsub : treeCylinder n t ⊆ treeCylinder n u
      · rw [if_pos hsub, treeFunction_apply_of_mem n u (hsub hαt), mul_one]
      · have huN : u ∈ N := Finset.mem_filter.mpr ⟨hu, hsub⟩
        rw [if_neg hsub, treeFunction_apply_of_notMem n u (hαN u huN), mul_zero]
    have hsum : 1 ≤ ∑ u ∈ C, w u := by
      have hdomα := hdom α
      change treeFunction n t α ≤ treeOperator n w α at hdomα
      rw [treeFunction_apply_of_mem n t hαt, hoperator] at hdomα
      exact hdomα
    calc
      a ≤ a * ∑ u ∈ C, w u := by nlinarith
      _ = ∑ u ∈ C, a * w u := by rw [Finset.mul_sum]
      _ ≤ ∑ u ∈ C,
          (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) * |w u| := by
        apply Finset.sum_le_sum
        intro u huC
        have hsub := (Finset.mem_filter.mp huC).2
        have hlevel := level_le_of_treeCylinder_subset hsub
        have hweight : a ≤ (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) := by
          apply zpow_le_zpow_right₀ (by norm_num)
          exact neg_le_neg (by exact_mod_cast hlevel)
        rw [abs_of_nonneg (hw u)]
        exact mul_le_mul_of_nonneg_right hweight (hw u)
      _ ≤ ∑ u ∈ w.support,
          (2 : ℝ) ^ (-(TreeNode.level u : ℤ)) * |w u| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro u _ _
        exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)
      _ = treeRho n w := by rw [treeRho, Finsupp.sum]
  refine ⟨hlower, ?_⟩
  apply le_antisymm
  · let w : TreeCoefficients n := treeBasis t
    have hw : 0 ≤ w := by simp [w, treeBasis]
    have hmajor : |treeFunction n t| ≤ treeOperator n w := by
      rw [abs_of_nonneg (treeFunction_nonneg n t)]
      change treeFunction n t ≤ treeOperator n (treeBasis t)
      rw [treeBasis, treeOperator_single, one_smul]
    calc
      treeSeminorm n (treeFunction n t) ≤ treeRho n w :=
        treeSeminorm_le_of_majorant n _ w hw hmajor
      _ = a := by simp [w, treeBasis, treeRho, a]
  · apply le_csInf (treeAdmissible_nonempty n (treeFunction n t))
    rintro r ⟨w, hw, hmajor, rfl⟩
    apply hlower w hw
    simpa [abs_of_nonneg (treeFunction_nonneg n t)] using hmajor
end OrderClosures
