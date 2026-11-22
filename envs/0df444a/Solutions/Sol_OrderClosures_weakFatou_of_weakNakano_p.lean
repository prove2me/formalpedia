-- Prove2me | solution 1 for OrderClosures.weakFatou_of_weakNakano_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:03.69447+00:00
-- url     : https://prove2.me/submissions/2d503285-1f45-4c7b-88ac-fb9f44956cec

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
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
public import Theorems.Thm_OrderConvergesTo_nonneg
public import Theorems.Thm_OrderConvergesTo_smul
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
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderClosures
theorem _root_.solution
    {Y : Type u} [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] (p : PaperLatticeNorm Y) {K : ℝ}
    (hNak : IsWeakNakanoConstant (X := Y) p K) :
    HasWeakFatouProperty p K := by
  refine ⟨hNak.1, ?_⟩
  intro ι _ _ _ f x hfmono hfpos hflub c hfc
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hc : 0 ≤ c := (p.nonneg (f i₀)).trans (hfc i₀)
  by_cases hc0 : c = 0
  · subst c
    have hfzero : ∀ i, f i = 0 := by
      intro i
      apply p.eq_zero_iff (f i) |>.1
      exact le_antisymm (hfc i) (p.nonneg _)
    have hxzero : x = 0 := by
      apply le_antisymm
      · apply hflub.2
        rintro _ ⟨i, rfl⟩
        simp [hfzero i]
      · simpa [hfzero i₀] using hflub.1 ⟨i₀, rfl⟩
    rw [hxzero]
    rw [p.eq_zero_iff 0 |>.2 rfl]
    simp
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let A : Set Y := Set.range fun i ↦ c⁻¹ • f i
  have hApos : A ⊆ Set.Ici 0 := by
    rintro _ ⟨i, rfl⟩
    exact smul_nonneg (inv_nonneg.mpr hc) (hfpos i)
  have hAdir : DirectedOn (· ≤ ·) A := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨c⁻¹ • f k, ⟨k, rfl⟩, ?_, ?_⟩
    · exact smul_le_smul_of_nonneg_left (hfmono hik) (inv_nonneg.mpr hc)
    · exact smul_le_smul_of_nonneg_left (hfmono hjk) (inv_nonneg.mpr hc)
  have hAbdd : BddAbove A := by
    refine ⟨c⁻¹ • x, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact smul_le_smul_of_nonneg_left (hflub.1 ⟨i, rfl⟩) (inv_nonneg.mpr hc)
  have hAp : ∀ z ∈ A, p z ≤ 1 := by
    rintro _ ⟨i, rfl⟩
    rw [p.smul, abs_of_pos (inv_pos.mpr hcpos), inv_mul_le_one₀ hcpos]
    exact hfc i
  obtain ⟨y, hypos, hyupper, hyp⟩ :=
    hNak.2 A hApos hAdir hAbdd hAp (δ / c) (div_pos hδ hcpos)
  have hxy : x ≤ c • y := by
    apply hflub.2
    rintro _ ⟨i, rfl⟩
    have hi := hyupper (c⁻¹ • f i) ⟨i, rfl⟩
    have := smul_le_smul_of_nonneg_left hi hc
    simpa [smul_smul, hc0] using this
  have hxpos : 0 ≤ x := (hfpos i₀).trans (hflub.1 ⟨i₀, rfl⟩)
  have hcyp : 0 ≤ c • y := smul_nonneg hc hypos
  have hpxy : p x ≤ p (c • y) := by
    apply p.solid
    simpa [abs_of_nonneg hxpos, abs_of_nonneg hcyp] using hxy
  calc
    p x ≤ p (c • y) := hpxy
    _ = c * p y := by rw [p.smul, abs_of_pos hcpos]
    _ ≤ c * (K + δ / c) := mul_le_mul_of_nonneg_left hyp hc
    _ = K * c + δ := by field_simp
end OrderClosures
