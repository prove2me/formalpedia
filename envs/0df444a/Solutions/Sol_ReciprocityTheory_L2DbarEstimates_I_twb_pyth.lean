-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.twb_pyth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:25:52.646336+00:00
-- url     : https://prove2.me/submissions/82461a20-6a0b-4d72-a9bb-b0c30664a6fd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (w G : α → ℂ) (ρ : α → ℝ)
    (hw : Measurable w) (hG : Measurable G) (hρm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    (hwf : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 * ρ x) ∂μ < ⊤)
    (hGf : ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2 * ρ x) ∂μ < ⊤)
    (horth : ∫ x, w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ) ∂μ = 0) :
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 * ρ x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (‖w x - G x‖ ^ 2 * ρ x) ∂μ := by
  have hA0 : ∀ x, 0 ≤ ‖w x‖ ^ 2 * ρ x := fun x => mul_nonneg (sq_nonneg _) (hρ x)
  have hB0 : ∀ x, 0 ≤ ‖G x‖ ^ 2 * ρ x := fun x => mul_nonneg (sq_nonneg _) (hρ x)
  have hC0 : ∀ x, 0 ≤ ‖w x - G x‖ ^ 2 * ρ x := fun x => mul_nonneg (sq_nonneg _) (hρ x)
  have hAm : Measurable (fun x => ‖w x‖ ^ 2 * ρ x) := (hw.norm.pow_const 2).mul hρm
  have hBm : Measurable (fun x => ‖G x‖ ^ 2 * ρ x) := (hG.norm.pow_const 2).mul hρm
  have hAi : Integrable (fun x => ‖w x‖ ^ 2 * ρ x) μ :=
    ⟨hAm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hA0)).2 hwf⟩
  have hBi : Integrable (fun x => ‖G x‖ ^ 2 * ρ x) μ :=
    ⟨hBm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hB0)).2 hGf⟩
  have hPm : Measurable (fun x => w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)) :=
    (hw.mul (Complex.continuous_conj.measurable.comp hG)).mul
      (Complex.measurable_ofReal.comp hρm)
  have hPi : Integrable (fun x => w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)) μ := by
    refine (hAi.add hBi).mono' hPm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hρ x)]
    nlinarith [mul_nonneg (sq_nonneg (‖w x‖ - ‖G x‖)) (hρ x),
      mul_nonneg (mul_nonneg (norm_nonneg (w x)) (norm_nonneg (G x))) (hρ x)]
  have hPre := Complex.reCLM.integrable_comp hPi
  simp only [Complex.reCLM_apply] at hPre
  have hre : ∀ x, ‖w x - G x‖ ^ 2 * ρ x = ‖w x‖ ^ 2 * ρ x + ‖G x‖ ^ 2 * ρ x
      - 2 * (w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)).re := by
    intro x
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im]
    ring
  have hCi : Integrable (fun x => ‖w x - G x‖ ^ 2 * ρ x) μ := by
    refine ((hAi.add hBi).sub (hPre.const_mul 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hre x]
  have hP0 : ∫ x, (w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)).re ∂μ = 0 := by
    have h1 := Complex.reCLM.integral_comp_comm hPi
    simp only [Complex.reCLM_apply] at h1
    rw [h1, horth, Complex.zero_re]
  have hint : ∫ x, ‖w x - G x‖ ^ 2 * ρ x ∂μ = ∫ x, ‖w x‖ ^ 2 * ρ x ∂μ + ∫ x, ‖G x‖ ^ 2 * ρ x ∂μ := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hre)]
    rw [integral_sub, integral_add, integral_const_mul, hP0, mul_zero, sub_zero]
    all_goals first | exact hAi | exact hBi | exact hAi.add hBi | exact hPre.const_mul 2
  rw [← ofReal_integral_eq_lintegral_ofReal hAi (Filter.Eventually.of_forall hA0),
    ← ofReal_integral_eq_lintegral_ofReal hCi (Filter.Eventually.of_forall hC0)]
  apply ENNReal.ofReal_le_ofReal
  rw [hint]
  linarith [integral_nonneg (μ := μ) (f := fun x => ‖G x‖ ^ 2 * ρ x) (fun x => hB0 x)]
end ReciprocityTheory.L2DbarEstimates.I
