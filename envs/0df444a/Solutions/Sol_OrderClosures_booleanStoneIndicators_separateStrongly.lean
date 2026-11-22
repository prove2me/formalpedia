-- Prove2me | solution 1 for OrderClosures.booleanStoneIndicators_separateStrongly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:18.892818+00:00
-- url     : https://prove2.me/submissions/acddb114-0c98-4763-8a0a-65dea2200ea9

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
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
open Set
noncomputable section
open OrderClosures
universe u v
variable (B : Type u) [CompleteBooleanAlgebra B]
namespace OrderClosures
theorem _root_.solution
    (Z : VectorSublattice C(BooleanStone B, ℝ))
    (hOne : (1 : C(BooleanStone B, ℝ)) ∈ Z)
    (hIndicator : ∀ b, booleanStoneIndicator B b ∈ Z) :
    (Z : Set C(BooleanStone B, ℝ)).SeparatesPointsStrongly := by
  intro v x y
  by_cases hxy : x = y
  · subst y
    refine ⟨v x • (1 : C(BooleanStone B, ℝ)),
      Z.toSubmodule.smul_mem (v x) hOne, ?_, ?_⟩
    all_goals simp
  · have hxyfun : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hxyfun
    cases hxb : x.1 b <;> cases hyb : y.1 b
    · exact False.elim (hb (by simp [hxb, hyb]))
    · let g := (v y - v x) • booleanStoneIndicator B b +
          v x • (1 : C(BooleanStone B, ℝ))
      refine ⟨g, Z.add_mem
        (Z.toSubmodule.smul_mem (v y - v x) (hIndicator b))
        (Z.toSubmodule.smul_mem (v x) hOne), ?_, ?_⟩
      · simp [g, booleanStoneIndicator_apply, hxb]
      · simp [g, booleanStoneIndicator_apply, hyb]
    · let g := (v x - v y) • booleanStoneIndicator B b +
          v y • (1 : C(BooleanStone B, ℝ))
      refine ⟨g, Z.add_mem
        (Z.toSubmodule.smul_mem (v x - v y) (hIndicator b))
        (Z.toSubmodule.smul_mem (v y) hOne), ?_, ?_⟩
      · simp [g, booleanStoneIndicator_apply, hxb]
      · simp [g, booleanStoneIndicator_apply, hyb]
    · exact False.elim (hb (by simp [hxb, hyb]))
end OrderClosures
