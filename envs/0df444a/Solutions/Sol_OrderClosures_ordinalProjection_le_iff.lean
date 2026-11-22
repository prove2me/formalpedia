-- Prove2me | solution 1 for OrderClosures.ordinalProjection_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:56.86693+00:00
-- url     : https://prove2.me/submissions/a6393ee7-f6a6-43c1-990c-8667a0a4959a

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
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
public import Theorems.Thm_OrderClosures_cnfExtensionLE_partialOrder_and_subrelation
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
    (ξ : Ordinal.{u}) (a b : GaoIndex ξ) :
    ordinalProjection ξ a ≤ ordinalProjection ξ b ↔ cnfExtensionLE a.1 b.1 := by
  classical
  constructor
  · intro hab
    by_contra hrel
    let x : GaoIndex ξ → Bool := fun c ↦
      if cnfExtensionLE a.1 c.1 then true else false
    have hxmono : ∀ c d : GaoIndex ξ,
        cnfExtensionLT c.1 d.1 → x c ≤ x d := by
      intro c d hcd
      dsimp [x]
      by_cases hac : cnfExtensionLE a.1 c.1
      · rw [if_pos hac, if_pos]
        exact cnfExtensionLE_partialOrder_and_subrelation.1.trans
          a.1 c.1 d.1 hac (Or.inr hcd)
      · rw [if_neg hac]
        exact Bool.false_le _
    let xK : GaoCompactSpace ξ := ⟨x, hxmono⟩
    have habx := hab xK
    have hxa : xK.1 a = true := by
      simp [xK, x, cnfExtensionLE]
    have hxb : xK.1 b = false := by
      simp [xK, x, hrel]
    simp only [ordinalProjection, hxa, hxb, Bool.false_eq_true, ↓reduceIte] at habx
    norm_num at habx
  · intro hab x
    rcases hab with hab | hab
    · have : a = b := Subtype.ext hab
      subst b
      exact le_rfl
    · dsimp [ordinalProjection]
      by_cases hxa : x.1 a = true
      · have hxb : x.1 b = true := by
          have hx := Bool.le_iff_imp.mp (x.2 a b hab)
          have hx' : True → x.1 b = true := by
            simpa only [hxa, Bool.true_eq] using hx
          exact hx' trivial
        simp only [hxa, hxb, ite_true]
        norm_num
      · simp only [hxa]
        positivity
end OrderClosures
