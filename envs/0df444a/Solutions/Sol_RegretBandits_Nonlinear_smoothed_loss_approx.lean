-- Prove2me | solution 1 for RegretBandits.Nonlinear.smoothed_loss_approx
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:01:22.874763+00:00
-- url     : https://prove2.me/submissions/1b459f4d-5245-4a7a-957c-1241e4414aef

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

open MeasureTheory
open scoped NNReal

open RegretBandits.Nonlinear in
theorem uniformBall_isProb_3b846a89 (d : ℕ) : IsProbabilityMeasure (uniformBall d) := by
  constructor
  have h0 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume _ one_pos).ne'
  have h1 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  simp only [uniformBall, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 h1

open RegretBandits.Nonlinear in
theorem uniformBall_ae_3b846a89 (d : ℕ) :
    ∀ᵐ b ∂(uniformBall d), b ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  unfold uniformBall
  apply Measure.ae_smul_measure
  exact ae_restrict_mem measurableSet_closedBall

open RegretBandits.Nonlinear NNReal in
theorem solution {d : ℕ} (hd : 1 ≤ d) (G : ℝ≥0)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ) (hℓ : LipschitzWith G ℓ)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin d)) :
    |ℓ x - smoothedLoss d δ ℓ x| ≤ δ * G := by
  have := uniformBall_isProb_3b846a89 d
  have hcont : Continuous (fun b : EuclideanSpace ℝ (Fin d) => ℓ (x + δ • b)) :=
    hℓ.continuous.comp (continuous_const.add (continuous_id.const_smul δ))
  have hint : Integrable (fun b : EuclideanSpace ℝ (Fin d) => ℓ (x + δ • b)) (uniformBall d) := by
    unfold uniformBall
    apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr
      (Metric.measure_closedBall_pos volume _ one_pos).ne')
    exact hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have heq : ℓ x - smoothedLoss d δ ℓ x
      = ∫ b, (ℓ x - ℓ (x + δ • b)) ∂(uniformBall d) := by
    rw [integral_sub (integrable_const _) hint, integral_const, probReal_univ, one_smul]
    rfl
  rw [heq, ← Real.norm_eq_abs]
  have hb : ∀ᵐ b ∂(uniformBall d), ‖ℓ x - ℓ (x + δ • b)‖ ≤ δ * G := by
    filter_upwards [uniformBall_ae_3b846a89 d] with b hbm
    have hn : ‖b‖ ≤ 1 := by simpa using hbm
    have h1 := hℓ.dist_le_mul x (x + δ • b)
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs]
    have h2 : dist x (x + δ • b) = δ * ‖b‖ := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hδ.le]
    rw [h2] at h1
    have hG : (0 : ℝ) ≤ G := G.2
    nlinarith [mul_le_mul_of_nonneg_left hn hδ.le]
  have := norm_integral_le_of_norm_le_const hb
  simpa [probReal_univ] using this
