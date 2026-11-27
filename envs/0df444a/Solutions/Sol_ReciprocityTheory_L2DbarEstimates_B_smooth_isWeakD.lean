-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.smooth_isWeakD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:32.592197+00:00
-- url     : https://prove2.me/submissions/4c96b55c-db61-4d8d-adad-e97ff24be3bb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_FderivMollApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise
namespace ReciprocityTheory.L2DbarEstimates.B
theorem _root_.solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : SmoothWeakSt E μ := by
  intro m c v g hg
  have hgd : ∀ k, Differentiable ℝ (g k) := fun k => (hg k).differentiable (by simp)
  have hgc : ∀ k, Continuous (fun x => fderiv ℝ (g k) x (v k)) := fun k =>
    ((hg k).continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun k => (hg k).continuous.locallyIntegrable, ?_, ?_⟩
  · have hc : Continuous (Dop c v g) := by
      unfold Dop
      exact continuous_finset_sum _ fun k _ => continuous_const.mul (hgc k)
    exact hc.locallyIntegrable
  · intro φ hφ hφc
    have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hφ' : ∀ k, Continuous (fun x => fderiv ℝ φ x (v k)) := fun k =>
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφ'c : ∀ k, HasCompactSupport (fun x => fderiv ℝ φ x (v k)) := fun k =>
      (hφc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℂ => L (v k)) (by simp)
    have int1 : ∀ k, Integrable (fun x => fderiv ℝ (g k) x (v k) * φ x) μ := fun k =>
      ((hgc k).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have int2 : ∀ k, Integrable (fun x => g k x * fderiv ℝ φ x (v k)) μ := fun k =>
      ((hg k).continuous.mul (hφ' k)).integrable_of_hasCompactSupport (hφ'c k).mul_left
    have int3 : ∀ k, Integrable (fun x => g k x * φ x) μ := fun k =>
      ((hg k).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have hibp : ∀ k, ∫ x, g k x * fderiv ℝ φ x (v k) ∂μ =
        -∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ := fun k =>
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (int1 k) (int2 k) (int3 k)
        (fun x _ => hgd k x) (fun x _ => hφd x)
    have hsum : ∫ x, Dop c v g x * φ x ∂μ =
        ∑ k, c k * ∫ x, fderiv ℝ (g k) x (v k) * φ x ∂μ := by
      simp only [Dop, Finset.sum_mul]
      rw [integral_finset_sum _ fun k _ => by simpa [mul_assoc] using (int1 k).const_mul (c k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_const_mul]
      congr 1
      ext x
      ring
    rw [hsum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hibp k, mul_neg, neg_neg]
end ReciprocityTheory.L2DbarEstimates.B
