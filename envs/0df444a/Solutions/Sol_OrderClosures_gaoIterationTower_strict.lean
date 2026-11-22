-- Prove2me | solution 1 for OrderClosures.gaoIterationTower_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:36.889804+00:00
-- url     : https://prove2.me/submissions/69c64cea-35ac-45e7-868b-f59f7c387989

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_gaoProjection_stage
public import Theorems.Thm_OrderClosures_gaoInclusion_stage
public import Theorems.Thm_OrderClosures_one_add_le_add_one_ordinal
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
public import Theorems.Thm_OrderClosures_gao_orderAdherence_stage_formula
public import Theorems.Thm_OrderClosures_ordinalProjection_strict_stage
public import Theorems.Thm_OrderClosures_subset_orderAdherence
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
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    ∀ η < Ordinal.lift.{u + 1, u} (Cardinal.ord (Order.succ κ)),
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η ⊂
        (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage (Order.succ η) := by
  classical
  intro η hη
  obtain ⟨δ, hδ, hδη⟩ := Ordinal.lt_lift_iff.mp hη
  have hκsucc : Cardinal.aleph0 ≤ Order.succ κ := hκ.trans (Order.le_succ κ)
  have hlimit := Cardinal.isSuccLimit_ord hκsucc
  let β : GaoComponentIndex κ := ⟨Order.succ δ, hlimit.succ_lt hδ⟩
  let C := canonicalOrderAdherenceTower (GaoStageSet β.1 1)
  have hδβ : δ ≤ β.1 := by
    dsimp only [β]
    exact Order.le_succ δ
  have hδoneβ : δ + 1 ≤ β.1 := by
    dsimp only [β]
    rw [Order.succ_eq_add_one]
  have hgamma : 1 + δ ≤ β.1 :=
    (one_add_le_add_one_ordinal δ).trans hδoneβ
  obtain ⟨ζ, hζnext, hζprev⟩ := ordinalProjection_strict_stage β.1 (1 + δ) hgamma
  let p := ordinalProjection β.1 ζ
  have hCδ := gao_orderAdherence_stage_formula β.1 C δ hδβ
  have hCnext := gao_orderAdherence_stage_formula β.1 C (δ + 1) hδoneβ
  have hpCnext : p ∈ C.stage (Ordinal.lift.{u + 1, u} (δ + 1)) := by
    rw [hCnext]
    simpa only [p, add_assoc] using hζnext
  have hpCprev : p ∉ C.stage (Ordinal.lift.{u + 1, u} δ) := by
    rw [hCδ]
    exact hζprev
  have hliftnext : Ordinal.lift.{u + 1, u} (δ + 1) = Order.succ η := by
    rw [Order.succ_eq_add_one, Ordinal.lift_add_one, hδη]
  let q := gaoProductInclusion κ β p
  have hqnext : q ∈
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage (Order.succ η) := by
    rw [← hliftnext]
    exact gaoInclusion_stage κ hκ β _ ⟨p, hpCnext, rfl⟩
  have hqprev : q ∉
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η := by
    intro hq
    have hproj := gaoProjection_stage κ hκ β η ⟨q, hq, rfl⟩
    have hp : p ∈ C.stage η := by
      simpa [q, gaoProductProjection, gaoProductInclusion] using hproj
    rw [← hδη] at hp
    exact hpCprev hp
  rw [Set.ssubset_iff_exists]
  refine ⟨?_, q, hqnext, hqprev⟩
  intro x hx
  rw [(canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage_succ]
  exact subset_orderAdherence _ hx
end OrderClosures
