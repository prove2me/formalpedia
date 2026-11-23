-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.closIneq_lint_ip_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:04.87411+00:00
-- url     : https://prove2.me/submissions/43236c4f-cd12-477a-975e-10f8ba85b542

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Closure
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [MeasurableSpace M] {n : ℕ} (μ : Measure M) (φ : M → ℝ)
    (hφ : Measurable φ) (v h : M → V n) (hv : AEStronglyMeasurable v μ)
    (hh : AEStronglyMeasurable h μ) :
    (∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ) ^ 2 ≤
      (∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-φ x)) ∂μ) *
        ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (-φ x)) ∂μ := by
  set F : M → ENNReal := fun x => ENNReal.ofReal (‖v x‖ * Real.exp (-φ x / 2)) with hFd
  set G : M → ENNReal := fun x => ENNReal.ofReal (‖h x‖ * Real.exp (-φ x / 2)) with hGd
  have hpt : ∀ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ≤ F x * G x := by
    intro x
    rw [hFd, hGd]
    dsimp only
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-φ x) = Real.exp (-φ x / 2) * Real.exp (-φ x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖⟪v x, h x⟫_ℂ‖ * Real.exp (-φ x) ≤ ‖v x‖ * ‖h x‖ * Real.exp (-φ x) :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (Real.exp_pos _).le
      _ = ‖v x‖ * Real.exp (-φ x / 2) * (‖h x‖ * Real.exp (-φ x / 2)) := by
          rw [he]
          ring
  have hsq2 : ∀ (a : ℝ) (x : M), (a * Real.exp (-φ x / 2)) ^ 2 = a ^ 2 * Real.exp (-φ x) := by
    intro a x
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hF2 : ∀ x, F x ^ (2 : ℝ) = ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-φ x)) := by
    intro x
    rw [hFd]
    dsimp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, hsq2]
  have hG2 : ∀ x, G x ^ (2 : ℝ) = ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (-φ x)) := by
    intro x
    rw [hGd]
    dsimp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, hsq2]
  have hsq : ∀ A : ENNReal, (A ^ (1 / (2 : ℝ))) ^ 2 = A := by
    intro A
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hE : Measurable fun x => Real.exp (-φ x / 2) := (hφ.neg.div_const 2).exp
  have hFm : AEMeasurable F μ := (hv.norm.aemeasurable.mul hE.aemeasurable).ennreal_ofReal
  have hGm : AEMeasurable G μ := (hh.norm.aemeasurable.mul hE.aemeasurable).ennreal_ofReal
  have hint : (∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ) ≤ ∫⁻ x, (F * G) x ∂μ :=
    lintegral_mono fun x => hpt x
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) (by constructor <;> norm_num) hFm hGm
  calc (∫⁻ x, ‖⟪v x, h x⟫_ℂ * (Real.exp (-φ x) : ℂ)‖ₑ ∂μ) ^ 2
      ≤ ((∫⁻ x, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (zero_le) (hint.trans hH) 2
    _ = (∫⁻ x, F x ^ (2 : ℝ) ∂μ) * ∫⁻ x, G x ^ (2 : ℝ) ∂μ := by
        rw [mul_pow, hsq, hsq]
    _ = _ := by
        simp only [hF2, hG2]
end ReciprocityTheory.L2DbarEstimates.F
