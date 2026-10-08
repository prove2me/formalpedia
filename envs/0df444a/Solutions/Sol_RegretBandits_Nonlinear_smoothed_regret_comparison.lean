-- Prove2me | solution 1 for RegretBandits.Nonlinear.smoothed_regret_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:49:54.637982+00:00
-- url     : https://prove2.me/submissions/3335bfc8-74e7-4bcd-ad6a-bade545d8770

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

set_option autoImplicit false

open MeasureTheory
open scoped NNReal Pointwise

namespace RegretBandits.Nonlinear.SRC8a

open RegretBandits.Nonlinear

lemma uniformBall_isProb (d : ℕ) : IsProbabilityMeasure (uniformBall d) := by
  constructor
  have h0 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume _ one_pos).ne'
  have h1 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  simp only [uniformBall, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 h1

lemma ae_mem_ball (d : ℕ) :
    ∀ᵐ b ∂(uniformBall d), b ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  unfold uniformBall
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_closedBall) _

lemma lip_bound {d : ℕ} {G : ℝ≥0} {ℓ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hℓ : LipschitzWith G ℓ) (u v : EuclideanSpace ℝ (Fin d)) :
    |ℓ u - ℓ v| ≤ G * ‖u - v‖ := by
  have := hℓ.dist_le_mul u v
  rwa [Real.dist_eq, dist_eq_norm] at this

lemma smoothed_close {d : ℕ} {G : ℝ≥0} {ℓ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hℓ : LipschitzWith G ℓ) {δ : ℝ} (hδ : 0 ≤ δ) (y : EuclideanSpace ℝ (Fin d)) :
    |smoothedLoss d δ ℓ y - ℓ y| ≤ δ * G := by
  have := uniformBall_isProb d
  have hb : ∀ᵐ b ∂(uniformBall d), ‖ℓ (y + δ • b) - ℓ y‖ ≤ δ * G := by
    filter_upwards [ae_mem_ball d] with b hb
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    rw [Real.norm_eq_abs]
    calc |ℓ (y + δ • b) - ℓ y| ≤ G * ‖y + δ • b - y‖ := lip_bound hℓ _ _
      _ = G * (δ * ‖b‖) := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
      _ ≤ G * (δ * 1) := by gcongr
      _ = δ * G := by ring
  have hcont : Continuous (fun b : EuclideanSpace ℝ (Fin d) => ℓ (y + δ • b)) :=
    hℓ.continuous.comp (by fun_prop)
  have hint : Integrable (fun b => ℓ (y + δ • b) - ℓ y) (uniformBall d) :=
    Integrable.of_bound (hcont.sub continuous_const).aestronglyMeasurable (δ * G) hb
  have hint2 : Integrable (fun b => ℓ (y + δ • b)) (uniformBall d) := by
    refine (hint.add (integrable_const (ℓ y))).congr ?_
    filter_upwards with b
    simp
  have heq : smoothedLoss d δ ℓ y - ℓ y = ∫ b, (ℓ (y + δ • b) - ℓ y) ∂(uniformBall d) := by
    rw [integral_sub hint2 (integrable_const _), integral_const]
    simp [smoothedLoss]
  rw [heq, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const hb
  simpa using this

end RegretBandits.Nonlinear.SRC8a

open MeasureTheory NNReal Pointwise RegretBandits.Nonlinear in
theorem solution {d : ℕ} (hd : 1 ≤ d)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : K ⊆ Metric.closedBall 0 R)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (δ : ℝ) (hδ : 0 < δ) (G : ℝ≥0)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hℓlip : ∀ t, LipschitzWith G (ℓ t))
    (hℓdiff : ∀ t, Differentiable ℝ (ℓ t)) (hℓconv : ∀ t, ConvexOn ℝ Set.univ (ℓ t))
    (xs : ℕ → EuclideanSpace ℝ (Fin d)) (hxs : ∀ t, xs t ∈ (1 - ξ) • K)
    (S : ℕ → EuclideanSpace ℝ (Fin d)) (hS : ∀ t, ‖S t‖ = 1)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ K) :
    (1 / 2) * ∑ t ∈ Finset.Icc 1 n, (ℓ t (xs t + δ • S t) + ℓ t (xs t - δ • S t))
        - ∑ t ∈ Finset.Icc 1 n, ℓ t x ≤
      ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (ℓ t) (xs t)
        - ∑ t ∈ Finset.Icc 1 n, smoothedLoss d δ (ℓ t) ((1 - ξ) • x)
        + 3 * δ * G * n + ξ * G * R * n := by
  have hxR : ‖x‖ ≤ R := by
    have := hKR hx
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hG : (0 : ℝ) ≤ G := G.2
  have key : ∀ t, (1 / 2) * (ℓ t (xs t + δ • S t) + ℓ t (xs t - δ • S t)) - ℓ t x ≤
      smoothedLoss d δ (ℓ t) (xs t) - smoothedLoss d δ (ℓ t) ((1 - ξ) • x)
        + (3 * δ * G + ξ * G * R) := by
    intro t
    have h1 := RegretBandits.Nonlinear.SRC8a.lip_bound (hℓlip t) (xs t + δ • S t) (xs t)
    have h2 := RegretBandits.Nonlinear.SRC8a.lip_bound (hℓlip t) (xs t - δ • S t) (xs t)
    have h3 := RegretBandits.Nonlinear.SRC8a.lip_bound (hℓlip t) x ((1 - ξ) • x)
    have h4 := RegretBandits.Nonlinear.SRC8a.smoothed_close (hℓlip t) hδ.le (xs t)
    have h5 := RegretBandits.Nonlinear.SRC8a.smoothed_close (hℓlip t) hδ.le ((1 - ξ) • x)
    have e1 : ‖xs t + δ • S t - xs t‖ = δ := by
      rw [add_sub_cancel_left, norm_smul, hS t, Real.norm_eq_abs, abs_of_pos hδ, mul_one]
    have e2 : ‖xs t - δ • S t - xs t‖ = δ := by
      rw [sub_sub_cancel_left, norm_neg, norm_smul, hS t, Real.norm_eq_abs, abs_of_pos hδ,
        mul_one]
    have e3 : ‖x - (1 - ξ) • x‖ ≤ ξ * R := by
      have : x - (1 - ξ) • x = ξ • x := by rw [sub_smul, one_smul, sub_sub_cancel]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
      exact mul_le_mul_of_nonneg_left hxR hξ0
    rw [e1] at h1
    rw [e2] at h2
    have h3' : ℓ t x - ℓ t ((1 - ξ) • x) ≤ G * (ξ * R) :=
      (le_abs_self _).trans (h3.trans (mul_le_mul_of_nonneg_left e3 hG))
    have a1 := (abs_le.mp h1).2
    have a2 := (abs_le.mp h2).2
    have a4 := (abs_le.mp h4).1
    have a5 := (abs_le.mp h5).2
    nlinarith [abs_le.mp h3]
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.Icc 1 n) => key t)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  linarith
