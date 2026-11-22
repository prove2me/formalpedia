-- Prove2me | solution 1 for OrderClosures.gaoStage_succ_subset_orderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:13.530798+00:00
-- url     : https://prove2.me/submissions/5c34f7df-e738-476a-8a8a-2519d9e1e81b

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Theorems.Thm_OrderClosures_gaoIndex_approximation
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
public import Theorems.Thm_OrderClosures_cnfExtensionLE_partialOrder_and_subrelation
public import Theorems.Thm_OrderClosures_isSolid_gaoStageSet
public import Theorems.Thm_OrderClosures_isSolid_orderAdherence
public import Theorems.Thm_OrderClosures_ordinalProjection_chain_iSup
public import Theorems.Thm_OrderClosures_ordinalProjection_le_iff
public import Theorems.Thm_OrderClosures_subset_orderAdherence
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_of_monotone_isLUB
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
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    GaoStageSet ξ (γ + 1) ⊆ orderAdherence (GaoStageSet ξ γ) := by
  classical
  intro f hf
  obtain ⟨ζ, hζstage, hfζ⟩ := hf
  by_cases hleast : leastCNFExponent ζ.1 < γ
  · exact subset_orderAdherence (GaoStageSet ξ γ)
      ⟨ζ, ⟨hζstage.1, hleast⟩, hfζ⟩
  have hleastLe : leastCNFExponent ζ.1 ≤ γ := by
    rw [← Order.succ_eq_add_one] at hζstage
    exact Order.lt_succ_iff.mp hζstage.2
  have hleastEq : leastCNFExponent ζ.1 = γ :=
    le_antisymm hleastLe (le_of_not_gt hleast)
  obtain ⟨Z, hZne, hZstage, hZchain, hvalLUB⟩ :=
    gaoIndex_approximation ξ γ hγ ζ hζstage.1 hleastEq
  have hprojLUB := ordinalProjection_chain_iSup ξ Z ζ hZne hZchain hvalLUB
  let : Nonempty Z := hZne.to_subtype
  let p : Z → C(GaoCompactSpace ξ, ℝ) := fun η ↦ ordinalProjection ξ η.1
  have hpmono : Monotone p := by
    intro η θ hηθ
    apply (ordinalProjection_le_iff ξ η.1 θ.1).2
    rcases hZchain η.2 θ.2 with h | h
    · exact h
    · have hOrd := cnfExtensionLE_partialOrder_and_subrelation.2 h
      exact Or.inl (le_antisymm hηθ hOrd)
  have hpLUB : IsLUB (Set.range p) (ordinalProjection ξ ζ) := by
    have hsets : Set.range p = ordinalProjection ξ '' Z := by
      ext g
      constructor
      · rintro ⟨η, rfl⟩
        exact ⟨η.1, η.2, rfl⟩
      · rintro ⟨η, hηZ, rfl⟩
        exact ⟨⟨η, hηZ⟩, rfl⟩
    rw [hsets]
    exact hprojLUB
  have hprojAdh : ordinalProjection ξ ζ ∈ orderAdherence (GaoStageSet ξ γ) := by
    refine ⟨Z, inferInstance, inferInstance, inferInstance, p, ?_,
      orderConvergesTo_of_monotone_isLUB hpmono hpLUB⟩
    intro η
    refine ⟨η.1, hZstage η.1 η.2, ?_⟩
    have hnonneg : 0 ≤ ordinalProjection ξ η.1 := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    rw [abs_of_nonneg hnonneg]
  apply isSolid_orderAdherence (isSolid_gaoStageSet ξ γ) hprojAdh
  have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
    intro x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  simpa only [abs_of_nonneg hnonneg] using hfζ
end OrderClosures
