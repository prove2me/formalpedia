-- Prove2me | solution 1 for OrderClosures.continuousMap_orderConvergesTo_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:17.160806+00:00
-- url     : https://prove2.me/submissions/f1f0cd30-1686-4fe6-94ce-c67111d37708

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
public import Theorems.Thm_OrderConvergesTo_le
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
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
namespace OrderClosures
theorem _root_.solution
    {ι : Type v} [Preorder ι] {f : ι → C(K, ℝ)} {x : C(K, ℝ)}
    (hfx : Filter.Tendsto f Filter.atTop (nhds x)) :
    OrderConvergesTo f x := by
  let r : ℕ → C(K, ℝ) := fun n ↦
    ContinuousMap.const K (((n : ℝ) + 1)⁻¹)
  have hranti : Antitone r := by
    intro m n hmn y
    simp only [r]
    exact inv_anti₀ (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hrnonneg : ∀ n, (0 : C(K, ℝ)) ≤ r n := by
    intro n y
    simp only [r]
    exact inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  have hscalar : Filter.Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹))
      Filter.atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hrglb : IsGLB (Set.range r) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact hrnonneg n
    · intro z hz y
      apply ge_of_tendsto' hscalar
      intro n
      simpa [r] using hz ⟨n, rfl⟩ y
  let κ := ULift.{u} ℕ
  let r' : κ → C(K, ℝ) := fun n ↦ r n.down
  have hrange : Set.range r' = Set.range r := by
    ext z
    simp only [Set.mem_range, r']
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.down, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨ULift.up n, rfl⟩
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r', ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact hranti hmn
  · intro n
    exact hrnonneg n.down
  · rw [hrange]
    exact hrglb
  intro k
  have hkpos : 0 < (((k.down : ℝ) + 1)⁻¹) := by positivity
  have hevent : ∀ᶠ n in Filter.atTop,
      f n ∈ Metric.ball x (((k.down : ℝ) + 1)⁻¹) :=
    hfx (Metric.ball_mem_nhds x hkpos)
  filter_upwards [hevent] with n hn
  intro y
  have hnorm : ‖f n - x‖ < (((k.down : ℝ) + 1)⁻¹) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hn
  calc
    |(f n - x) y| ≤ ‖f n - x‖ := by
      simpa only [Real.norm_eq_abs] using
        (ContinuousMap.norm_coe_le_norm (f n - x) y)
    _ ≤ (((k.down : ℝ) + 1)⁻¹) := hnorm.le
    _ = r' k y := by simp [r', r]
end OrderClosures
