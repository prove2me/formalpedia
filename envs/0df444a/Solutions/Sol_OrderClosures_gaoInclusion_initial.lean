-- Prove2me | solution 1 for OrderClosures.gaoInclusion_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:04.507606+00:00
-- url     : https://prove2.me/submissions/abc24426-3a31-4062-889e-4f193c5e114f

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_gaoIterationProduct_abs_fst
public import Theorems.Thm_OrderClosures_gaoIterationProduct_abs_snd
public import Theorems.Thm_OrderClosures_gaoComponentGenerator_embedding
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
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) :
    gaoProductInclusion κ β '' GaoStageSet β.1 1 ⊆ gaoIterationSet κ hκ := by
  classical
  rintro _ ⟨x, ⟨ζ, hζ, hx⟩, rfl⟩
  let ζ' : GaoSuccessorGenerator β.1 := ⟨ζ, hζ⟩
  let a := gaoGeneratorEmbedding κ hκ β.1 β.2 ζ'
  refine ⟨gaoGlobalGenerator κ hκ a, ⟨a, rfl⟩, ?_⟩
  constructor
  · intro γ
    rw [gaoIterationProduct_abs_fst, gaoIterationProduct_abs_fst]
    by_cases hγ : γ = β
    · subst γ
      simp only [gaoProductInclusion, gaoGlobalGenerator, Pi.single_eq_same]
      rw [gaoComponentGenerator_embedding]
      have hnonneg : 0 ≤ ordinalProjection β.1 ζ := by
        intro y
        simp only [ordinalProjection]
        split_ifs <;> norm_num
      dsimp only [ζ']
      rw [abs_of_nonneg hnonneg]
      exact hx
    · change |(Pi.single
          (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1) β x) γ| ≤
        |gaoComponentGenerator κ hκ γ a|
      rw [Pi.single_eq_of_ne hγ]
      simp
  · intro b
    rw [gaoIterationProduct_abs_snd, gaoIterationProduct_abs_snd]
    simp only [gaoProductInclusion, gaoGlobalGenerator, Pi.zero_apply]
    simp
end OrderClosures
