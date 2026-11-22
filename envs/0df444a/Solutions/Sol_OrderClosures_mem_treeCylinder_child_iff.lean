-- Prove2me | solution 1 for OrderClosures.mem_treeCylinder_child_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:58.672948+00:00
-- url     : https://prove2.me/submissions/69eeef92-51cd-41d7-84f7-c9799e37b50c

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
public import Theorems.Thm_OrderConvergesTo_le
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
    (n : ℕ) (t : TreeNode n) (ht : TreeNode.level t < n) (m : ℕ)
    (α : TreeProduct n) :
    α ∈ treeCylinder n (TreeNode.child t ht m) ↔
      α ∈ treeCylinder n t ∧ α ⟨t, ht⟩ ≤ m := by
  constructor
  · intro h
    constructor
    · intro j
      let j' : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨j, by
          simp [TreeNode.level, TreeNode.child]⟩
      have hj := h j'
      have hpref : strictPrefix (TreeNode.child t ht m) j' = strictPrefix t j := by
        apply Subtype.ext
        apply Subtype.ext
        exact List.take_append_of_le_length j.isLt.le
      have hget : (TreeNode.child t ht m).1.get j' = t.1.get j := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left j.isLt
      rw [hpref, hget] at hj
      exact hj
    · let j : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨TreeNode.level t, by simp [TreeNode.level, TreeNode.child]⟩
      have hj := h j
      have hpref : strictPrefix (TreeNode.child t ht m) j = ⟨t, ht⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        simp [j, strictPrefix, TreeNode.restrict, TreeNode.level, TreeNode.child]
      have hget : (TreeNode.child t ht m).1.get j = m := by
        simp [j, TreeNode.level, TreeNode.child]
      rw [hpref, hget] at hj
      exact hj
  · rintro ⟨h, hlast⟩ j
    by_cases hj : (j : ℕ) < TreeNode.level t
    · let j' : Fin (TreeNode.level t) := ⟨j, hj⟩
      have hprefix := h j'
      have hpref : strictPrefix (TreeNode.child t ht m) j = strictPrefix t j' := by
        apply Subtype.ext
        apply Subtype.ext
        exact List.take_append_of_le_length hj.le
      have hget : (TreeNode.child t ht m).1.get j = t.1.get j' := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        exact List.getElem_append_left hj
      rw [hpref, hget]
      exact hprefix
    · have hjeq : (j : ℕ) = TreeNode.level t := by
        have hjlt : (j : ℕ) < TreeNode.level t + 1 := by
          simpa [TreeNode.level, TreeNode.child] using j.isLt
        omega
      let jlast : Fin (TreeNode.level (TreeNode.child t ht m)) :=
        ⟨TreeNode.level t, by simp [TreeNode.level, TreeNode.child]⟩
      have hjlast : j = jlast := Fin.ext hjeq
      rw [hjlast]
      have hpref : strictPrefix (TreeNode.child t ht m) jlast = ⟨t, ht⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        simp [jlast, strictPrefix, TreeNode.restrict, TreeNode.level, TreeNode.child]
      have hget : (TreeNode.child t ht m).1.get jlast = m := by
        simp [jlast, TreeNode.level, TreeNode.child]
      rw [hpref, hget]
      exact hlast
end OrderClosures
