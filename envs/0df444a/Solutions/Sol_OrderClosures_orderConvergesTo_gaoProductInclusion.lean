-- Prove2me | solution 1 for OrderClosures.orderConvergesTo_gaoProductInclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:08.134215+00:00
-- url     : https://prove2.me/submissions/1262e0be-25cf-4598-85f9-d27f5cdd42f4

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
    {i : Type v} [Preorder i] {f : i → GaoComponent β.1}
    {x : GaoComponent β.1} (hfx : OrderConvergesTo f x) :
    OrderConvergesTo (fun j ↦ gaoProductInclusion κ β (f j))
      (gaoProductInclusion κ β x) := by
  classical
  rcases hfx with ⟨τ, hτpre, hτdir, hτne, r, hranti, hrnonneg, hrglb, hbound⟩
  let : Preorder τ := hτpre
  let : IsDirected τ (· ≤ ·) := hτdir
  let : Nonempty τ := hτne
  refine ⟨τ, inferInstance, inferInstance, inferInstance,
    fun k ↦ gaoProductInclusion κ β (r k), ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    constructor
    · intro γ
      by_cases hγ : γ = β
      · subst γ
        simpa [gaoProductInclusion] using hranti hkl
      · simp [gaoProductInclusion, hγ]
    · exact le_rfl
  · intro k
    constructor
    · intro γ
      by_cases hγ : γ = β
      · subst γ
        simpa [gaoProductInclusion] using hrnonneg k
      · simp [gaoProductInclusion, hγ]
    · exact le_rfl
  · constructor
    · rintro _ ⟨k, rfl⟩
      constructor
      · intro γ
        by_cases hγ : γ = β
        · subst γ
          simpa [gaoProductInclusion] using hrglb.1 ⟨k, rfl⟩
        · simp [gaoProductInclusion, hγ]
      · exact le_rfl
    · intro w hw
      constructor
      · intro γ
        by_cases hγ : γ = β
        · subst γ
          apply hrglb.2
          rintro _ ⟨k, rfl⟩
          simpa [gaoProductInclusion] using (hw ⟨k, rfl⟩).1 β
        · obtain ⟨k⟩ := (inferInstance : Nonempty τ)
          simpa [gaoProductInclusion, hγ] using
            (hw ⟨k, rfl⟩).1 γ
      · intro a
        obtain ⟨k⟩ := (inferInstance : Nonempty τ)
        simpa [gaoProductInclusion] using (hw ⟨k, rfl⟩).2 a
  · intro k
    exact (hbound k).mono fun j hj ↦ by
      constructor
      · intro γ
        change |((Pi.single
            (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1) β (f j) -
          Pi.single (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1) β x) γ)| ≤
            (Pi.single (M := fun δ : GaoComponentIndex κ ↦ GaoComponent δ.1)
              β (r k)) γ
        by_cases hγ : γ = β
        · subst γ
          simpa only [Pi.sub_apply, Pi.single_eq_same] using hj
        · simp [hγ]
      · intro a
        change |((0 : ULift.{u + 1, u} (Cardinal.ord κ).ToType → ℝ) a - 0)| ≤ 0
        simp
end OrderClosures
