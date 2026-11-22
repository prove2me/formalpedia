-- Prove2me | solution 1 for P2M_Auto_eLpNorm_carlesonF__le_0be6ee33c933
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:32.717083+00:00
-- url     : https://prove2.me/submissions/5fdd4ae8-171a-47a7-8d7a-5ef8680e0bb7

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_isCompact_carlesonBox
public import Theorems.Thm_P2M_Auto_carlesonF__eq_zero_fe95b4220c40
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {g : ℝ → ℂ} {L B : ℝ} (hB : 0 ≤ B) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hg : ∀ x, L < |x| → g x = 0) :
    (eLpNorm (carlesonF₁ g) 3 volume).toReal ≤
      B * (volume (carlesonBox L)).toReal ^ (1 / 3 : ℝ) := by
  set K := carlesonBox L
  have hle : eLpNorm (carlesonF₁ g) 3 volume ≤ eLpNorm (K.indicator fun _ => (B : ℂ)) 3 volume := by
    refine eLpNorm_mono fun p => ?_
    by_cases hp : p ∈ K
    · rw [indicator_of_mem hp, carlesonF₁, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs B, abs_of_nonneg hB, Real.norm_eq_abs,
        abs_of_nonneg carlesonBump₁.nonneg]
      exact (mul_le_of_le_one_right (norm_nonneg _) carlesonBump₁.le_one).trans (hgB _)
    · rw [carlesonF₁_eq_zero hg hp]
      simp
  have hfin : volume K ≠ (⊤ : ℝ≥0∞) := (isCompact_carlesonBox L).measure_lt_top.ne
  calc (eLpNorm (carlesonF₁ g) 3 volume).toReal
      ≤ (‖(B : ℂ)‖ₑ * volume K ^ (1 / (3 : ℝ≥0∞).toReal)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin))
          (hle.trans (eLpNorm_indicator_const_le _ 3))
    _ = B * (volume K).toReal ^ (1 / 3 : ℝ) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
        simp [abs_of_nonneg hB]
end Auto
