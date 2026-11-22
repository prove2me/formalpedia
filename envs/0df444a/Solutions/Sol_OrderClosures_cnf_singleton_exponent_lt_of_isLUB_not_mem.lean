-- Prove2me | solution 1 for OrderClosures.cnf_singleton_exponent_lt_of_isLUB_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:38.095103+00:00
-- url     : https://prove2.me/submissions/65b79653-2202-4966-8180-2ed9a2188faa

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Theorems.Thm_OrderClosures_cnf_singleton_spec
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
public import Theorems.Thm_OrderConvergesTo_le
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
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u})
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) (haQ : a ∉ Q)
    {q β c γ d : Ordinal.{u}} (hqQ : q ∈ Q)
    (hq : Ordinal.CNF Ordinal.omega0 q = [(β, c)])
    (ha : Ordinal.CNF Ordinal.omega0 a = [(γ, d)]) : β < γ := by
  obtain ⟨hqeq, hcpos, hclt, hlogq⟩ := cnf_singleton_spec hq
  obtain ⟨haeq, hdpos, hdlt, hloga⟩ := cnf_singleton_spec ha
  have hqa : q ≤ a := hlub.1 hqQ
  have hqne : q ≠ a := fun h ↦ haQ (h ▸ hqQ)
  have hqalt : q < a := lt_of_le_of_ne hqa hqne
  have hβγ : β ≤ γ := by
    have := Ordinal.log_mono_right Ordinal.omega0 hqa
    simpa only [hlogq, hloga] using this
  apply hβγ.lt_of_ne
  intro hβγeq
  subst β
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hclt
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hdlt
  have hmpos : 0 < m := by exact_mod_cast hcpos
  have hnpos : 0 < n := by exact_mod_cast hdpos
  have hmn : m < n := by
    by_contra h
    have hnm : n ≤ m := le_of_not_gt h
    have hmul : Ordinal.omega0 ^ γ * (n : Ordinal) ≤
        Ordinal.omega0 ^ γ * (m : Ordinal) :=
      mul_le_mul_right (by exact_mod_cast hnm) _
    have hmulLt : Ordinal.omega0 ^ γ * (m : Ordinal) <
        Ordinal.omega0 ^ γ * (n : Ordinal) := by
      rw [← hβγeq, ← hqeq, hβγeq, ← haeq]
      exact hqalt
    exact (not_le_of_gt hmulLt) hmul
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  have hkpos : 0 < k := lt_of_lt_of_le hmpos (Nat.le_of_lt_succ hmn)
  let b : Ordinal.{u} := Ordinal.omega0 ^ γ * (k : Ordinal)
  have hbUpper : b ∈ upperBounds Q := by
    intro r hrQ
    obtain ⟨ε, e, hr⟩ := hsingle r hrQ
    obtain ⟨hreq, hepos, helt, hlogr⟩ := cnf_singleton_spec hr
    have hra : r ≤ a := hlub.1 hrQ
    have hrne : r ≠ a := fun h ↦ haQ (h ▸ hrQ)
    have hralt : r < a := lt_of_le_of_ne hra hrne
    have hεγ : ε ≤ γ := by
      have := Ordinal.log_mono_right Ordinal.omega0 hra
      simpa only [hlogr, hloga] using this
    rcases hεγ.eq_or_lt with rfl | hεγlt
    · obtain ⟨j, rfl⟩ := Ordinal.lt_omega0.mp helt
      have hjlt : j < k + 1 := by
        by_contra h
        have hle : k + 1 ≤ j := le_of_not_gt h
        have hmul : Ordinal.omega0 ^ ε * ((k + 1 : ℕ) : Ordinal) ≤
            Ordinal.omega0 ^ ε * (j : Ordinal) :=
          mul_le_mul_right (by exact_mod_cast hle) _
        have hmulLt : Ordinal.omega0 ^ ε * (j : Ordinal) <
            Ordinal.omega0 ^ ε * ((k + 1 : ℕ) : Ordinal) := by
          rw [← hreq, ← haeq]
          exact hralt
        exact (not_le_of_gt hmulLt) hmul
      dsimp [b]
      rw [hreq]
      exact mul_le_mul_right (by exact_mod_cast (Nat.le_of_lt_succ hjlt)) _
    · have hr0 : r ≠ 0 := by
        intro hzero
        rw [hzero, Ordinal.CNF.zero_right] at hr
        simp at hr
      have hrpow : r < Ordinal.omega0 ^ γ :=
        (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hr0).2 (by
          simpa only [hlogr] using hεγlt)
      exact hrpow.le.trans (by
        dsimp [b]
        exact Ordinal.le_mul_left _ (by exact_mod_cast hkpos))
  have hab : a ≤ b := hlub.2 hbUpper
  have hba : b < a := by
    dsimp [b]
    rw [haeq]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (Nat.lt_succ_self k))
      (Ordinal.opow_pos γ Ordinal.omega0_pos)
  exact (not_le_of_gt hba) hab
end OrderClosures
