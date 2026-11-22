-- Prove2me | solution 1 for OrderClosures.CNFStep.trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:28.489777+00:00
-- url     : https://prove2.me/submissions/b36aa16c-33ae-4954-9c10-81db8a090de6

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
public import Theorems.Thm_ClosedOrderIdeal_mem_sInf
public import Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
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
attribute [local simp] ClosedOrderIdeal.inf_toSubmodule
attribute [local simp] ClosedOrderIdeal.mem_sInf
attribute [local simp] ClosedOrderIdeal.sup_toSubmodule
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
open Set
universe u v
namespace OrderClosures
namespace CNFStep
theorem _root_.solution {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y z : Ordinal.{u} × Ordinal.{u}}
    (hxy : CNFStep pre x y) (hxz : CNFStep pre x z) :
    y = z ∨ CNFStep pre y z ∨ CNFStep pre z y := by
  rcases x with ⟨β, c⟩
  rcases y with ⟨γ, d⟩
  rcases z with ⟨δ, e⟩
  simp only [CNFStep] at hxy hxz ⊢
  rcases hxy with ⟨rfl, hcd⟩ | ⟨hβγ, hγ⟩ <;>
    rcases hxz with ⟨rfl, hce⟩ | ⟨hβδ, hδ⟩
  · rcases lt_trichotomy d e with hde | rfl | hed
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, hde⟩))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hed⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hβδ, hδ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hβγ, hγ⟩))
  · rcases lt_trichotomy γ δ with hγδ | hγδ | hδγ
    · exact Or.inr (Or.inl (Or.inr ⟨hγδ, hδ⟩))
    · subst δ
      rcases lt_trichotomy d e with hde | rfl | hed
      · exact Or.inr (Or.inl (Or.inl ⟨rfl, hde⟩))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hed⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hδγ, hγ⟩))
end CNFStep
end OrderClosures
