-- Prove2me | solution 1 for OrderClosures.component_large_iterated_adherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:15.493807+00:00
-- url     : https://prove2.me/submissions/0dc2738a-1892-4a6a-b87e-c50a4222a7f7

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
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
public import Theorems.Thm_OrderClosures_component_basic
public import Theorems.Thm_OrderClosures_component_weakFatou
public import Theorems.Thm_OrderClosures_treeFunction_child_properties
public import Theorems.Thm_OrderConvergesTo_smul
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_of_monotone_isLUB
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
      HasWeakFatouProperty (componentLatticeNorm n) 2 ∧
      ((2 : ℝ) ^ n • componentRoot n) ∈
        iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) n ∧
      componentLatticeNorm n ((2 : ℝ) ^ n • componentRoot n) = (2 : ℝ) ^ n := by
  have hiter : ∀ k : ℕ, ∀ t : TreeNode n, TreeNode.level t + k = n →
      ((2 : ℝ) ^ n • componentTreeFunction n t) ∈
        iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k := by
    intro k
    induction k with
    | zero =>
        intro t ht
        have hlevel : TreeNode.level t = n := by omega
        change componentLatticeNorm n ((2 : ℝ) ^ n • componentTreeFunction n t) ≤ 1
        rw [(componentLatticeNorm n).smul, abs_of_pos (pow_pos (by norm_num) n),
          (component_basic n).2.2.2 t hlevel]
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
        norm_num
    | succ k ih =>
        intro t ht
        have ht_nonterminal : TreeNode.level t < n := by omega
        let f : ℕ → TreeComponent n := fun m ↦
          (2 : ℝ) ^ n • componentTreeFunction n (TreeNode.child t ht_nonterminal m)
        have hf : ∀ m, f m ∈
            iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k := by
          intro m
          apply ih
          have hlevelchild : TreeNode.level (TreeNode.child t ht_nonterminal m) =
              TreeNode.level t + 1 := by simp [TreeNode.child, TreeNode.level]
          rw [hlevelchild]
          omega
        have hchild := treeFunction_child_properties n t ht_nonterminal
        have hmono : Monotone
            (fun m ↦ componentTreeFunction n (TreeNode.child t ht_nonterminal m)) := by
          intro a b hab
          exact hchild.2.1 hab
        have hlub : IsLUB
            (Set.range fun m ↦ componentTreeFunction n
              (TreeNode.child t ht_nonterminal m)) (componentTreeFunction n t) := by
          constructor
          · rintro _ ⟨m, rfl⟩
            exact hchild.1 m |>.2
          · intro z hz
            change treeFunction n t ≤ z.1
            apply hchild.2.2.2
            rintro _ ⟨m, rfl⟩
            exact hz ⟨m, rfl⟩
        change ((2 : ℝ) ^ n • componentTreeFunction n t) ∈ orderAdherence
          (iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k)
        refine ⟨ℕ, inferInstance, inferInstance, inferInstance, f, hf, ?_⟩
        simpa [f] using
          (orderConvergesTo_of_monotone_isLUB hmono hlub).smul ((2 : ℝ) ^ n)
  have hroot : componentTreeFunction n (TreeNode.root n) = componentRoot n := rfl
  have hmembership : ((2 : ℝ) ^ n • componentRoot n) ∈
      iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) n := by
    rw [← hroot]
    apply hiter n (TreeNode.root n)
    simp [TreeNode.root, TreeNode.level]
  have hnorm : componentLatticeNorm n ((2 : ℝ) ^ n • componentRoot n) =
      (2 : ℝ) ^ n := by
    rw [(componentLatticeNorm n).smul, abs_of_pos (pow_pos (by norm_num) n),
      (component_basic n).2.2.1, mul_one]
  exact ⟨(component_basic n).1, (component_basic n).2.1,
    (component_weakFatou n).2, hmembership, hnorm⟩
end OrderClosures
