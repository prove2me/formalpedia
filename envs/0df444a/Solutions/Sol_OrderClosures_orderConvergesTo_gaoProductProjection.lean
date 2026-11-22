-- Prove2me | solution 1 for OrderClosures.orderConvergesTo_gaoProductProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:56.938812+00:00
-- url     : https://prove2.me/submissions/f1a36dde-4dba-4eb5-b8f4-c87d8074f80b

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
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
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ)
    {i : Type v} [Preorder i] {f : i → GaoIterationProduct κ}
    {x : GaoIterationProduct κ} (hfx : OrderConvergesTo f x) :
    OrderConvergesTo (fun j ↦ gaoProductProjection κ β (f j))
      (gaoProductProjection κ β x) := by
  classical
  rcases hfx with ⟨τ, hτpre, hτdir, hτne, r, hranti, hrnonneg, hrglb, hbound⟩
  let : Preorder τ := hτpre
  let : IsDirected τ (· ≤ ·) := hτdir
  let : Nonempty τ := hτne
  refine ⟨τ, inferInstance, inferInstance, inferInstance,
    fun k ↦ gaoProductProjection κ β (r k), ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    exact (hranti hkl).1 β
  · intro k
    exact (hrnonneg k).1 β
  · constructor
    · rintro _ ⟨k, rfl⟩
      exact (hrglb.1 ⟨k, rfl⟩).1 β
    · intro c hc
      let w : GaoIterationProduct κ := (Pi.single β c, 0)
      have hw : w ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        constructor
        · intro γ
          by_cases hγ : γ = β
          · subst γ
            simp only [w, Pi.single_eq_same]
            exact hc ⟨k, rfl⟩
          · simpa [w, hγ] using (hrnonneg k).1 γ
        · exact fun _ ↦ (hrnonneg k).2 _
      have hw0 := hrglb.2 hw
      simpa [w] using hw0.1 β
  · intro k
    exact (hbound k).mono fun j hj ↦ hj.1 β
end OrderClosures
