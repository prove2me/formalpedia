-- Prove2me | solution 1 for OrderClosures.ordinalProjection_strict_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:18.9538+00:00
-- url     : https://prove2.me/submissions/e976ee7e-4efa-47fc-ad9d-06cfa918ff1f

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
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
public import Theorems.Thm_OrderClosures_ordinalProjection_le_iff
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
    (ξ γ : Ordinal.{u}) (hγ : γ ≤ ξ) :
    ∃ ζ : GaoIndex ξ,
      ordinalProjection ξ ζ ∈ GaoStageSet ξ (γ + 1) ∧
        ordinalProjection ξ ζ ∉ GaoStageSet ξ γ := by
  have hpow : Ordinal.omega0 ^ γ ≤ Ordinal.omega0 ^ ξ :=
    Ordinal.opow_le_opow_right Ordinal.omega0_pos hγ
  let ζ : GaoIndex ξ := ⟨Ordinal.omega0 ^ γ,
    hpow.trans le_self_add⟩
  have hcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = [(γ, 1)] := by
    dsimp [ζ]
    simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
      (e := γ) (x := 1) (y := 0) Ordinal.one_lt_omega0 one_ne_zero
      Ordinal.one_lt_omega0 (Ordinal.opow_pos γ Ordinal.omega0_pos)
  have hleast : leastCNFExponent ζ.1 = γ := by
    simp [leastCNFExponent, hcnf]
  refine ⟨ζ, ?_, ?_⟩
  · refine ⟨ζ, ⟨hpow, ?_⟩, ?_⟩
    · rw [hleast]
      rw [Ordinal.lt_add_iff one_ne_zero]
      exact ⟨0, zero_lt_one, by simp⟩
    · have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
        intro x
        simp only [ordinalProjection]
        split_ifs <;> norm_num
      rw [abs_of_nonneg hnonneg]
  · rintro ⟨η, hη, hdom⟩
    have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    rw [abs_of_nonneg hnonneg] at hdom
    have hrel := (ordinalProjection_le_iff ξ ζ η).mp hdom
    rcases hrel with heq | hrel
    · have : leastCNFExponent η.1 = γ := by
        rw [← heq]
        exact hleast
      exact (lt_irrefl γ) (by simpa only [this] using hη.2)
    · rcases hrel with ⟨pre, tail, β, c, δ, d, hζcnf, hηcnf, hstep⟩
      rw [hcnf] at hζcnf
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hζcnf
          rcases hζcnf with ⟨hhead, rfl⟩
          have hβ : β = γ := congrArg Prod.fst hhead.symm
          have hc : c = 1 := congrArg Prod.snd hhead.symm
          subst β
          subst c
          have hγδ : γ ≤ δ := by
            rcases hstep with ⟨rfl, _⟩ | ⟨hγδ, _⟩
            · exact le_rfl
            · exact hγδ.le
          have hleastη : leastCNFExponent η.1 = δ := by
            simp [leastCNFExponent, hηcnf]
          exact (not_lt_of_ge (hleastη.symm ▸ hγδ)) hη.2
      | cons p pre =>
          simp only [List.cons_append, List.cons.injEq] at hζcnf
          rcases hζcnf with ⟨rfl, hfalse⟩
          simp at hfalse
end OrderClosures
