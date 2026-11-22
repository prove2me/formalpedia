-- Prove2me | solution 1 for OrderClosures.cnf_eq_singleton_of_isLUB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:12.559208+00:00
-- url     : https://prove2.me/submissions/41593034-0783-4773-a1d4-d28e61f1b5b2

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Theorems.Thm_OrderClosures_cnf_singleton_le_leadingCNFTerm
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
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u}) (hQ : Q.Nonempty)
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) :
    ∃ γ d, Ordinal.CNF Ordinal.omega0 a = [(γ, d)] := by
  obtain ⟨q, hqQ⟩ := hQ
  obtain ⟨γ, d, hq⟩ := hsingle q hqQ
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Ordinal.CNF.zero_right] at hq
    simp at hq
  have hqa : q ≤ a := hlub.1 hqQ
  have ha0 : a ≠ 0 := by
    intro ha
    apply hq0
    exact le_antisymm (ha ▸ hqa) (zero_le : (0 : Ordinal) ≤ q)
  have hleadUpper : leadingCNFTerm a ∈ upperBounds Q := by
    intro r hrQ
    obtain ⟨e, c, hr⟩ := hsingle r hrQ
    exact cnf_singleton_le_leadingCNFTerm hr (hlub.1 hrQ)
  have halead : a ≤ leadingCNFTerm a := hlub.2 hleadUpper
  have hleada : leadingCNFTerm a ≤ a := by
    exact Ordinal.mul_div_le a
      (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)
  have hleadeq : leadingCNFTerm a = a := le_antisymm hleada halead
  have hmod : a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) = 0 := by
    have hdiv := Ordinal.div_add_mod a
      (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)
    change leadingCNFTerm a +
      a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) = a at hdiv
    apply add_left_cancel (a := leadingCNFTerm a)
    calc
      leadingCNFTerm a + a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) =
          a := hdiv
      _ = leadingCNFTerm a + 0 := by rw [add_zero, hleadeq]
  refine ⟨Ordinal.log Ordinal.omega0 a,
    a / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a, ?_⟩
  rw [Ordinal.CNF.ne_zero ha0, hmod, Ordinal.CNF.zero_right]
end OrderClosures
