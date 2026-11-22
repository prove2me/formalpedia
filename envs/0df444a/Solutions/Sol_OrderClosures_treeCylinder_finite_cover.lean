-- Prove2me | solution 1 for OrderClosures.treeCylinder_finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:59.205164+00:00
-- url     : https://prove2.me/submissions/51c5cc90-a2aa-4dc6-bfb6-641a0045ee9b

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
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
public import Theorems.Thm_OrderConvergesTo_sup
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
    (n : ℕ) (t : TreeNode n) (F : Finset (TreeNode n))
    (hcover : ∀ α ∈ treeCylinder n t, ∃ u ∈ F, α ∈ treeCylinder n u) :
    ∃ u ∈ F, treeCylinder n t ⊆ treeCylinder n u := by
  classical
  by_contra hconcl
  push Not at hconcl
  let witness : ↥F → TreeProduct n := fun u ↦
    Classical.choose (Set.not_subset.mp (hconcl u.1 u.2))
  have hwitness_mem (u : ↥F) : witness u ∈ treeCylinder n t :=
    (Classical.choose_spec (Set.not_subset.mp (hconcl u.1 u.2))).1
  have hwitness_notMem (u : ↥F) : witness u ∉ treeCylinder n u.1 :=
    (Classical.choose_spec (Set.not_subset.mp (hconcl u.1 u.2))).2
  let α : TreeProduct n := fun q ↦ Finset.univ.sup fun u : ↥F ↦ witness u q
  have hαt : α ∈ treeCylinder n t := by
    intro j
    apply Finset.sup_le
    intro u _
    exact hwitness_mem u j
  obtain ⟨u, huF, hαu⟩ := hcover α hαt
  let uF : ↥F := ⟨u, huF⟩
  have hnot := hwitness_notMem uF
  simp only [treeCylinder, Set.mem_ofPred_eq] at hnot
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  have hle : witness uF (strictPrefix u j) ≤ α (strictPrefix u j) := by
    exact Finset.le_sup (s := Finset.univ)
      (f := fun v : ↥F ↦ witness v (strictPrefix u j)) (Finset.mem_univ uF)
  exact (not_lt_of_ge (hαu j)) (hj.trans_le hle)
end OrderClosures
