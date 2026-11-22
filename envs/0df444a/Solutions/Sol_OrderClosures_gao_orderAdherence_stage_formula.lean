-- Prove2me | solution 1 for OrderClosures.gao_orderAdherence_stage_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:58.068889+00:00
-- url     : https://prove2.me/submissions/5cb32084-5a88-4d9c-8050-f8c456b60c73

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Theorems.Thm_OrderClosures_orderAdherence_gaoStage
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
    (ξ : Ordinal.{u}) (T : OrderAdherenceTower (GaoStageSet ξ 1)) :
    ∀ β ≤ ξ, T.stage (Ordinal.lift.{u + 1, u} β) = GaoStageSet ξ (1 + β) := by
  intro β
  induction β using Ordinal.limitRecOn with
  | zero =>
      intro hzero
      simpa using T.stage_zero
  | add_one β ih =>
      intro hβ
      have hβξ : β ≤ ξ := le_self_add.trans hβ
      have hstage := ih hβξ
      have hnonzero : 1 + β ≠ 0 := by
        exact (zero_lt_one.trans_le (le_self_add : (1 : Ordinal) ≤ 1 + β)).ne'
      rw [show Ordinal.lift.{u + 1, u} (β + 1) =
          Order.succ (Ordinal.lift.{u + 1, u} β) by
            rw [Order.succ_eq_add_one, Ordinal.lift_add_one],
        T.stage_succ, hstage, orderAdherence_gaoStage ξ (1 + β) hnonzero,
        add_assoc]
  | limit β hβlim ih =>
      intro hβξ
      rw [T.stage_limit _ (Ordinal.isSuccLimit_lift.mpr hβlim)]
      ext f
      constructor
      · intro hf
        rcases Set.mem_iUnion.mp hf with ⟨η, hfη⟩
        obtain ⟨δ, hδη⟩ := Ordinal.mem_range_lift_of_le η.2.le
        have hδβ : δ < β := by
          have h := η.2
          rw [← hδη] at h
          exact Ordinal.lift_lt.mp h
        have hδξ : δ ≤ ξ := hδβ.le.trans hβξ
        have hfδ : f ∈ GaoStageSet ξ (1 + δ) := by
          rw [← ih δ hδβ hδξ]
          simpa only [hδη] using hfη
        obtain ⟨ζ, hζ, hfζ⟩ := hfδ
        exact ⟨ζ, ⟨hζ.1, hζ.2.trans_le (add_le_add_right hδβ.le 1)⟩, hfζ⟩
      · intro hf
        obtain ⟨ζ, hζ, hfζ⟩ := hf
        obtain ⟨δ, hδβ, hleastδ⟩ :=
          ((Ordinal.isNormal_add_right 1).lt_iff_exists_lt hβlim).mp hζ.2
        have hδξ : δ ≤ ξ := hδβ.le.trans hβξ
        apply Set.mem_iUnion.mpr
        let η : Set.Iio (Ordinal.lift.{u + 1, u} β) :=
          ⟨Ordinal.lift.{u + 1, u} δ, Ordinal.lift_lt.mpr hδβ⟩
        refine ⟨η, ?_⟩
        rw [ih δ hδβ hδξ]
        exact ⟨ζ, ⟨hζ.1, hleastδ⟩, hfζ⟩
end OrderClosures
