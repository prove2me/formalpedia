-- Prove2me | solution 1 for OrderClosures.cnfValue_cnfAddMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:49.255771+00:00
-- url     : https://prove2.me/submissions/0ada551a-c815-4031-bbe1-08777ea31c56

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_cnfValue_lt_opow
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
theorem _root_.solution
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hd : 0 < d) :
    cnfValue (cnfAddMonomial l γ d) =
      cnfValue l + Ordinal.omega0 ^ γ * d := by
  induction l with
  | nil => simp [cnfAddMonomial, cnfValue]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailLt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
        hlt p (List.mem_cons_of_mem (δ, e) hp)
      have htailExp : ∀ p ∈ l, p.1 < δ := fun p hp ↦
        hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have htailValue : cnfValue l < Ordinal.omega0 ^ δ :=
        cnfValue_lt_opow l hsorted.2 htailLt htailExp
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
        change Ordinal.omega0 ^ δ * e + cnfValue (cnfAddMonomial l γ d) =
          (Ordinal.omega0 ^ δ * e + cnfValue l) + Ordinal.omega0 ^ γ * d
        rw [ih hsorted.2 htailLt, add_assoc]
      · by_cases hγeqδ : γ = δ
        · subst γ
          simp only [cnfAddMonomial, hγδ, ↓reduceIte]
          simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
          change Ordinal.omega0 ^ δ * (e + d) =
            (Ordinal.omega0 ^ δ * e + cnfValue l) + Ordinal.omega0 ^ δ * d
          rw [mul_add, add_assoc,
            Ordinal.add_of_omega0_opow_le htailValue
              (Ordinal.le_mul_left _ hd)]
        · have hδγ : δ < γ :=
            lt_of_le_of_ne (le_of_not_gt hγδ) (Ne.symm hγeqδ)
          have hallExp : ∀ p ∈ (δ, e) :: l, p.1 < γ := by
            intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with hp | hp
            · simpa only [hp] using hδγ
            · exact (htailExp p hp).trans hδγ
          have hvalue : cnfValue ((δ, e) :: l) < Ordinal.omega0 ^ γ :=
            cnfValue_lt_opow ((δ, e) :: l)
              (by simpa only [List.map_cons, List.pairwise_cons] using hsorted)
              hlt hallExp
          simp only [cnfAddMonomial, hγδ, hγeqδ, ↓reduceIte]
          simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
          exact (Ordinal.add_of_omega0_opow_le hvalue
            (Ordinal.le_mul_left _ hd)).symm
end OrderClosures
