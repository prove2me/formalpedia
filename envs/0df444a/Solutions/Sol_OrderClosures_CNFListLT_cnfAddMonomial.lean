-- Prove2me | solution 1 for OrderClosures.CNFListLT_cnfAddMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:40.973097+00:00
-- url     : https://prove2.me/submissions/f1e121bd-82a4-49eb-a8bf-0cc9b8ac3796

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_cnfAddMonomial_exponents_lt
public import Theorems.Thm_OrderClosures_CNFStep_cons_prefix
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
    (l : List (Ordinal.{u} × Ordinal.{u})) (hne : l ≠ [])
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (β c : Ordinal.{u}) (hlast : l.getLast? = some (β, c))
    (γ d : Ordinal.{u}) (hdpos : 0 < d)
    (hβγ : β ≤ γ) :
    CNFListLT l (cnfAddMonomial l γ d) := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      cases l with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          rcases hlast with ⟨rfl, rfl⟩
          by_cases hγeqβ : γ = β
          · subst γ
            refine ⟨[], [], (β, c), (β, c + d), by simp,
              by simp [cnfAddMonomial], ?_⟩
            exact Or.inl ⟨rfl, lt_add_of_pos_right c hdpos⟩
          · have hβγ' : β < γ := lt_of_le_of_ne hβγ (Ne.symm hγeqβ)
            refine ⟨[], [], (β, c), (γ, d), by simp,
              by simp [cnfAddMonomial, hβγ'.not_gt, hγeqβ], ?_⟩
            exact Or.inr ⟨hβγ', Or.inl rfl⟩
      | cons q l =>
          simp only [List.map_cons, List.pairwise_cons] at hsorted
          have htailPos : ∀ p ∈ q :: l, 0 < p.2 := fun p hp ↦
            hpos p (List.mem_cons_of_mem (δ, e) hp)
          have htailLt : ∀ p ∈ q :: l, p.2 < Ordinal.omega0 := fun p hp ↦
            hlt p (List.mem_cons_of_mem (δ, e) hp)
          have htailSorted : (List.map Prod.fst (q :: l)).Pairwise
              (fun a b ↦ b < a) := by
            simpa only [List.map_cons, List.pairwise_cons] using hsorted.2
          have hlastTail : (q :: l).getLast? = some (β, c) := by
            simpa using hlast
          by_cases hγδ : γ < δ
          · rcases ih (by simp) htailSorted htailPos htailLt hlastTail with
              ⟨pre, tail, x, y, hin, hout, hstep⟩
            have hyMem : y ∈ cnfAddMonomial (q :: l) γ d := by
              rw [hout]
              exact List.mem_append_right _ (by simp)
            have hyδ : y.1 < δ :=
              cnfAddMonomial_exponents_lt (q :: l) γ d δ
                (fun p hp ↦ hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
                hγδ y hyMem
            refine ⟨(δ, e) :: pre, tail, x, y, ?_, ?_,
              CNFStep.cons_prefix hstep hyδ⟩
            · simpa only [List.cons_append] using
                congrArg (List.cons (δ, e)) hin
            · simp only [cnfAddMonomial, hγδ, ↓reduceIte]
              simpa only [cnfAddMonomial, hγδ, ↓reduceIte, List.cons_append] using
                congrArg (List.cons (δ, e)) hout
          · by_cases hγeqδ : γ = δ
            · subst γ
              refine ⟨[], q :: l, (δ, e), (δ, e + d), by simp,
                by simp [cnfAddMonomial], ?_⟩
              exact Or.inl ⟨rfl, lt_add_of_pos_right e hdpos⟩
            · have hδγ : δ < γ :=
                lt_of_le_of_ne (le_of_not_gt hγδ) (Ne.symm hγeqδ)
              refine ⟨[], q :: l, (δ, e), (γ, d), by simp,
                by simp [cnfAddMonomial, hγδ, hγeqδ], ?_⟩
              exact Or.inr ⟨hδγ, Or.inl rfl⟩
end OrderClosures
