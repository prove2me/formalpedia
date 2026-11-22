-- Prove2me | solution 1 for OrderClosures.cnfExtensionLT_add_singleton_of_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:20.378821+00:00
-- url     : https://prove2.me/submissions/e67a3e0d-d0a7-44fa-a934-14b0dd8ebc9a

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_CNF_cnfValue
public import Theorems.Thm_OrderClosures_CNF_cnfValue_add_monomial
public import Theorems.Thm_OrderClosures_CNFListLT_cnfAddMonomial
public import Theorems.Thm_OrderClosures_cnfExtensionLT_iff_CNFListLT
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
    {ζ q γ d β c : Ordinal.{u}}
    {pre : List (Ordinal.{u} × Ordinal.{u})}
    (hζ : Ordinal.CNF Ordinal.omega0 ζ = pre ++ [(β, c)])
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hβγ : β ≤ γ) : cnfExtensionLT ζ (ζ + q) := by
  let l := Ordinal.CNF Ordinal.omega0 ζ
  have hl : l = pre ++ [(β, c)] := hζ
  have hlne : l ≠ [] := by rw [hl]; simp
  have hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a) :=
    (Ordinal.CNF.sortedGT Ordinal.omega0 ζ).pairwise
  have hpos : ∀ p ∈ l, 0 < p.2 := fun p hp ↦
    Ordinal.CNF.snd_pos hp
  have hlt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
    Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hp
  have hlast : l.getLast? = some (β, c) := by rw [hl]; simp
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  have hζvalue : cnfValue l = ζ := Ordinal.CNF.foldr Ordinal.omega0 ζ
  have hqvalue : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  apply cnfExtensionLT_iff_CNFListLT.mpr
  rw [← hζvalue, hqvalue,
    CNF_cnfValue_add_monomial l hsorted hpos hlt γ d hdpos hdlt,
    CNF_cnfValue l hsorted hpos hlt]
  exact CNFListLT_cnfAddMonomial l hlne hsorted hpos hlt β c hlast
    γ d hdpos hβγ
end OrderClosures
