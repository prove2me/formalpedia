-- Prove2me | solution 1 for OrderClosures.cnfAddMonomial_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:21.02884+00:00
-- url     : https://prove2.me/submissions/3ea7fca4-044d-46b2-ad3b-1097d0963be0

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_cnfAddMonomial_exponents_lt
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
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    let out := cnfAddMonomial l γ d
    (out.map Prod.fst).Pairwise (fun a b ↦ b < a) ∧
      (∀ p ∈ out, 0 < p.2) ∧
      (∀ p ∈ out, p.2 < Ordinal.omega0) := by
  induction l with
  | nil => simp [cnfAddMonomial, hdpos, hdlt]
  | cons p l ih =>
      rcases p with ⟨δ, e⟩
      simp only [List.map_cons, List.pairwise_cons] at hsorted
      have htailPos : ∀ p ∈ l, 0 < p.2 := fun p hp ↦
        hpos p (List.mem_cons_of_mem (δ, e) hp)
      have htailLt : ∀ p ∈ l, p.2 < Ordinal.omega0 := fun p hp ↦
        hlt p (List.mem_cons_of_mem (δ, e) hp)
      obtain ⟨ihsorted, ihpos, ihlt⟩ :=
        ih hsorted.2 htailPos htailLt
      by_cases hγδ : γ < δ
      · simp only [cnfAddMonomial, hγδ, ↓reduceIte, List.map_cons,
          List.pairwise_cons]
        refine ⟨⟨?_, ihsorted⟩, ?_, ?_⟩
        · intro e' he'
          rw [List.mem_map] at he'
          obtain ⟨p, hp, rfl⟩ := he'
          exact cnfAddMonomial_exponents_lt l γ d δ
            (fun p hp ↦ hsorted.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)) hγδ p hp
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hpos (δ, e) (by simp)
          · exact ihpos p hp
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hlt (δ, e) (by simp)
          · exact ihlt p hp
      · by_cases hγeqδ : γ = δ
        · subst γ
          have hepos : 0 < e := hpos (δ, e) (by simp)
          have helt : e < Ordinal.omega0 := hlt (δ, e) (by simp)
          have hsumpos : 0 < e + d := hepos.trans_le (le_self_add)
          have hsumlt : e + d < Ordinal.omega0 := by
            obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp helt
            obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hdlt
            rw [← Nat.cast_add]
            exact Ordinal.natCast_lt_omega0 (m + n)
          simp [cnfAddMonomial, hsumpos, hsumlt]
        · simp [cnfAddMonomial, hγδ, hγeqδ, hdpos, hdlt]
end OrderClosures
