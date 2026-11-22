-- Prove2me | solution 1 for OrderClosures.CNFListLT.ordinal_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:56.441805+00:00
-- url     : https://prove2.me/submissions/1447b082-fc8a-4659-94fc-489e803f627a

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_cnfValue_lt_opow
public import Theorems.Thm_OrderClosures_cnfValue_append_lt_append
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
namespace CNFListLT
theorem _root_.solution {ζ ζ' : Ordinal.{u}}
    (h : CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
      (Ordinal.CNF Ordinal.omega0 ζ')) : ζ < ζ' := by
  rcases h with ⟨pre, tail, ⟨β, c⟩, ⟨γ, d⟩, hζ, hζ', hstep⟩
  have hsorted := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ).pairwise
  rw [hζ, List.map_append, List.map_cons, List.pairwise_append] at hsorted
  have hsuffix : ((β, c) :: tail).map Prod.fst |>.Pairwise (fun a b ↦ b < a) :=
    hsorted.2.1
  rw [List.map_cons, List.pairwise_cons] at hsuffix
  have hcoeff : ∀ p ∈ tail, p.2 < Ordinal.omega0 := by
    intro p hp
    apply Ordinal.CNF.snd_lt Ordinal.one_lt_omega0
    rw [hζ]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  have htail : cnfValue tail < Ordinal.omega0 ^ β :=
    cnfValue_lt_opow tail hsuffix.2 hcoeff (fun p hp ↦
      hsuffix.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hc : c < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (o := ζ) (x := (β, c)) Ordinal.one_lt_omega0
    rw [hζ]
    exact List.mem_append_right _ List.mem_cons_self
  have hd : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := ζ') (x := (γ, d))
    rw [hζ']
    exact List.mem_append_right _ (by simp)
  have hdiv : cnfValue ((β, c) :: tail) < cnfValue [(γ, d)] := by
    rcases hstep with ⟨rfl, hcd⟩ | ⟨hβγ, _⟩
    · simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
      exact Ordinal.opow_mul_add_lt_opow_mul htail hcd
    · simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
      exact (Ordinal.opow_mul_add_lt_opow hc htail hβγ).trans_le
        (Ordinal.le_mul_left _ hd)
  rw [← Ordinal.CNF.foldr Ordinal.omega0 ζ,
    ← Ordinal.CNF.foldr Ordinal.omega0 ζ']
  change cnfValue (Ordinal.CNF Ordinal.omega0 ζ) <
    cnfValue (Ordinal.CNF Ordinal.omega0 ζ')
  rw [hζ, hζ']
  exact cnfValue_append_lt_append pre _ _ hdiv
end CNFListLT
end OrderClosures
