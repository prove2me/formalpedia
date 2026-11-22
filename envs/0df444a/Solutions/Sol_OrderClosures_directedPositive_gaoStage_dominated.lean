-- Prove2me | solution 1 for OrderClosures.directedPositive_gaoStage_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:02.504822+00:00
-- url     : https://prove2.me/submissions/27eac04f-261b-4ed7-a3ed-4c30ec10ab86

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Theorems.Thm_OrderClosures_gaoDominators_nonempty
public import Theorems.Thm_OrderClosures_gaoDominator_above_minimal
public import Theorems.Thm_OrderClosures_gaoMinimalDominators_finite
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
public import Theorems.Thm_OrderClosures_cnfExtensionLE_linear_above
public import Theorems.Thm_OrderClosures_leastCNFExponent_chain_lub_le
public import Theorems.Thm_OrderClosures_ordinalProjection_chain_iSup
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
    (ξ γ : Ordinal.{u}) {z : C(GaoCompactSpace ξ, ℝ)}
    (hz : z ∈ directedPositiveAdherence (GaoStageSet ξ γ)) :
    ∃ α : GaoIndex ξ, α.1 ≤ Ordinal.omega0 ^ ξ ∧
      leastCNFExponent α.1 ≤ γ ∧ z ≤ ordinalProjection ξ α := by
  classical
  rcases hz with ⟨hz0, B, hBstage, hBne, hBdir, hBlub⟩
  by_cases hzero : z = 0
  · let α : GaoIndex ξ := ⟨0, by simp⟩
    refine ⟨α, by simp [α], by simp [α, leastCNFExponent], ?_⟩
    rw [hzero]
    intro x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  have hbne : ∃ b ∈ B, b ≠ 0 := by
    by_contra h
    have hzeroUpper : (0 : C(GaoCompactSpace ξ, ℝ)) ∈ upperBounds B := by
      intro b hb
      have hb0 := (hBstage hb).2
      have hbzero : b = 0 := by
        by_contra hbne'
        exact h ⟨b, hb, hbne'⟩
      rw [hbzero]
    exact hzero (le_antisymm (hBlub.2 hzeroUpper) hz0)
  obtain ⟨b₀, hb₀B, hb₀ne⟩ := hbne
  have hb₀0 : 0 ≤ b₀ := (hBstage hb₀B).2
  let M := gaoMinimalDominators ξ γ b₀
  have hMfin : M.Finite := gaoMinimalDominators_finite ξ γ hb₀0 hb₀ne
  have hMne : M.Nonempty := by
    obtain ⟨ζ, hζ⟩ := gaoDominators_nonempty ξ γ hb₀0 (hBstage hb₀B).1
    obtain ⟨μ, hμ, _⟩ := gaoDominator_above_minimal ξ γ hζ
    exact ⟨μ, hμ⟩
  let : Nonempty B := hBne.to_subtype
  let : IsDirectedOrder B := hBdir.isDirectedOrder
  let b₀B : B := ⟨b₀, hb₀B⟩
  let D : M → Set B := fun μ ↦
    {b | b₀ ≤ b.1 ∧ ∃ ζ ∈ gaoDominators ξ γ b.1,
      cnfExtensionLE μ.1.1 ζ.1}
  have hcover : ∀ b : B, b₀ ≤ b.1 → ∃ μ : M, b ∈ D μ := by
    intro b hb₀b
    have hb0 : 0 ≤ b.1 := (hBstage b.2).2
    obtain ⟨ζ, hζ⟩ := gaoDominators_nonempty ξ γ hb0 (hBstage b.2).1
    have hζ₀ : ζ ∈ gaoDominators ξ γ b₀ := ⟨hζ.1, hb₀b.trans hζ.2⟩
    obtain ⟨μ, hμ, hμζ⟩ := gaoDominator_above_minimal ξ γ hζ₀
    exact ⟨⟨μ, hμ⟩, hb₀b, ζ, hζ, hμζ⟩
  have hcofinal : ∃ μ : M, ∀ b : B, ∃ c ∈ D μ, b ≤ c := by
    by_contra h
    have hbad : ∀ μ : M, ∃ b : B, ∀ c ∈ D μ, ¬ b ≤ c := by
      intro μ
      have hμ : ¬ ∀ b : B, ∃ c ∈ D μ, b ≤ c := fun hμ ↦ h ⟨μ, hμ⟩
      push Not at hμ
      exact hμ
    choose w hw using hbad
    let : Fintype M := hMfin.fintype
    obtain ⟨d, hd⟩ := Finite.exists_le w
    obtain ⟨e, hde, hb₀e⟩ := exists_ge_ge d b₀B
    obtain ⟨μ, heD⟩ := hcover e hb₀e
    exact (hw μ e heD) ((hd μ).trans hde)
  obtain ⟨μ, hμcofinal⟩ := hcofinal
  have hDne : (D μ).Nonempty := by
    obtain ⟨c, hcD, _⟩ := hμcofinal b₀B
    exact ⟨c, hcD⟩
  let ζfun : D μ → GaoIndex ξ := fun b ↦ Classical.choose b.2.2
  have hζfun : ∀ b : D μ,
      ζfun b ∈ gaoDominators ξ γ b.1.1 ∧
        cnfExtensionLE μ.1.1 (ζfun b).1 := fun b ↦
    ⟨Classical.choose_spec b.2.2 |>.1,
      Classical.choose_spec b.2.2 |>.2⟩
  let Z : Set (GaoIndex ξ) := Set.range ζfun
  have hZne : Z.Nonempty := by
    obtain ⟨b, hb⟩ := hDne
    exact ⟨ζfun ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
  have hZchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1 := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    exact cnfExtensionLE_linear_above μ.1.1 (hζfun b).2 (hζfun c).2
  let a : Ordinal.{u} := sSup ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z)
  have hvalsne : ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z).Nonempty := hZne.image _
  have hvalsBdd : BddAbove ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) := by
    refine ⟨Ordinal.omega0 ^ ξ, ?_⟩
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (hζfun b).1.1.1
  have haLUB : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) a :=
    isLUB_csSup hvalsne hvalsBdd
  have hale : a ≤ Ordinal.omega0 ^ ξ := by
    apply haLUB.2
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (hζfun b).1.1.1
  let α : GaoIndex ξ := ⟨a, hale.trans le_self_add⟩
  have hprojLUB : IsLUB (ordinalProjection ξ '' Z)
      (ordinalProjection ξ α) :=
    ordinalProjection_chain_iSup ξ Z α hZne hZchain haLUB
  have hzα : z ≤ ordinalProjection ξ α := hBlub.2 (by
    intro b hbB
    obtain ⟨c, hcD, hbc⟩ := hμcofinal ⟨b, hbB⟩
    let cD : D μ := ⟨c, hcD⟩
    calc
      b ≤ c.1 := hbc
      _ ≤ ordinalProjection ξ (ζfun cD) := (hζfun cD).1.2
      _ ≤ ordinalProjection ξ α := hprojLUB.1 ⟨ζfun cD, ⟨cD, rfl⟩, rfl⟩)
  have hleast : leastCNFExponent α.1 ≤ γ := by
    apply leastCNFExponent_chain_lub_le ξ γ Z α hZne hZchain haLUB
    rintro _ ⟨b, rfl⟩
    exact (hζfun b).1.1.2
  exact ⟨α, hale, hleast, hzα⟩
end OrderClosures
