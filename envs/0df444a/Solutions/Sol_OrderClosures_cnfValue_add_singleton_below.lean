-- Prove2me | solution 1 for OrderClosures.cnfValue_add_singleton_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:25.988392+00:00
-- url     : https://prove2.me/submissions/e67ad41e-c764-4c31-baea-2e77461f5b8f

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
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
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderClosures_CNF_cnfValue_add_monomial
public import Theorems.Thm_OrderClosures_cnfAddMonomial_eq_append_of_lt_all
public import Theorems.Thm_OrderClosures_cnfValue_append
public import Theorems.Thm_OrderClosures_cnf_singleton_spec
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
    (pre : List (Ordinal.{u} × Ordinal.{u})) (γ : Ordinal.{u}) (n : ℕ)
    (hpreSorted : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x))
    (hpreAbove : ∀ x ∈ pre, γ < x.1)
    (hprePos : ∀ x ∈ pre, 0 < x.2)
    (hpreLt : ∀ x ∈ pre, x.2 < Ordinal.omega0)
    (q : Ordinal.{u}) (hq : q ∈ singletonCNFBelow γ) :
    ∃ δ d, Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧ δ < γ ∧
      Ordinal.CNF Ordinal.omega0
        (cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) + q) =
        if n = 0 then pre ++ [(δ, d)]
        else pre ++ (γ, (n : Ordinal)) :: [(δ, d)] := by
  obtain ⟨δ, d, hqcnf, hqpow⟩ := hq
  obtain ⟨hqeq, hdpos, hdlt, hlogq⟩ := cnf_singleton_spec hqcnf
  have hδγraw : Ordinal.log Ordinal.omega0 q < γ :=
    (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 (by
      rw [hqeq]
      exact mul_ne_zero (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero)
        hdpos.ne')).mp hqpow
  have hδγ : δ < γ := by simpa only [hlogq] using hδγraw
  refine ⟨δ, d, hqcnf, hδγ, ?_⟩
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, mul_zero, add_zero, ↓reduceIte]
    rw [hqeq, CNF_cnfValue_add_monomial pre hpreSorted hprePos hpreLt
      δ d hdpos hdlt, cnfAddMonomial_eq_append_of_lt_all pre δ d
        (fun x hx ↦ hδγ.trans (hpreAbove x hx))]
  · let l := pre ++ [(γ, (n : Ordinal))]
    have hnpos : 0 < (n : Ordinal) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hnlt : (n : Ordinal) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 n
    have hlsorted : (l.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
      dsimp [l]
      rw [List.map_append, List.pairwise_append]
      refine ⟨hpreSorted, by simp, ?_⟩
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      simp only [List.map_singleton, List.mem_singleton] at hb
      subst b
      exact hpreAbove x hx
    have hlpos : ∀ x ∈ l, 0 < x.2 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hprePos x hx
      · simp only [List.mem_singleton] at hx
        subst x
        exact hnpos
    have hllt : ∀ x ∈ l, x.2 < Ordinal.omega0 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpreLt x hx
      · simp only [List.mem_singleton] at hx
        subst x
        exact hnlt
    have hδl : ∀ x ∈ l, δ < x.1 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hδγ.trans (hpreAbove x hx)
      · simp only [List.mem_singleton] at hx
        subst x
        exact hδγ
    rw [if_neg hn]
    change Ordinal.CNF Ordinal.omega0
      ((cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal)) + q) =
        pre ++ (γ, (n : Ordinal)) :: [(δ, d)]
    have hlvalue : cnfValue l = cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) := by
      dsimp [l]
      rw [cnfValue_append]
      simp [cnfValue]
    rw [← hlvalue, hqeq,
      CNF_cnfValue_add_monomial l hlsorted hlpos hllt δ d hdpos hdlt,
      cnfAddMonomial_eq_append_of_lt_all l δ d hδl]
    simp [l, List.append_assoc]
end OrderClosures
