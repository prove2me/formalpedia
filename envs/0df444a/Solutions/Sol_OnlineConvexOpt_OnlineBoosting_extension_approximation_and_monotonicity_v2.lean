-- Prove2me | solution 1 for OnlineConvexOpt.OnlineBoosting.extension_approximation_and_monotonicity_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:15:37.88626+00:00
-- url     : https://prove2.me/submissions/db6a30ef-6ea6-4c4f-94a7-8c6cf8facb1f

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Extension
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.FirstOrder


namespace OnlineConvexOpt.OnlineBoosting

open MeasureTheory

lemma eamv2_avg_le {n : ℕ} (φ ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : Continuous φ)
    (hψ : Continuous ψ) (c : ℝ)
    (h : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, φ v ≤ ψ v + c) :
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
      ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, φ v ≤
    ((volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
      ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ψ v) + c := by
  set B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 with hB
  have hvpos : 0 < (volume B).toReal := by
    apply ENNReal.toReal_pos
    · exact (Metric.measure_closedBall_pos _ _ one_pos).ne'
    · exact measure_closedBall_lt_top.ne
  have hcomp : IsCompact B := isCompact_closedBall _ _
  have hiφ : IntegrableOn φ B := hφ.continuousOn.integrableOn_compact hcomp
  have hiψ : IntegrableOn ψ B := hψ.continuousOn.integrableOn_compact hcomp
  have hic : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => c) B :=
    integrableOn_const measure_closedBall_lt_top.ne
  have hle : ∫ v in B, φ v ≤ ∫ v in B, (ψ v + c) :=
    setIntegral_mono_on hiφ (hiψ.add hic) measurableSet_closedBall h
  rw [integral_add hiψ hic, setIntegral_const, smul_eq_mul,
    show volume.real B = (volume B).toReal from rfl] at hle
  have := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hvpos.le)
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul] at this
  exact this

lemma eamv2_avg_const {n : ℕ} (k : ℝ) :
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
      ∫ _v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, k = k := by
  have hvpos : 0 < (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    apply ENNReal.toReal_pos
    · exact (Metric.measure_closedBall_pos _ _ one_pos).ne'
    · exact measure_closedBall_lt_top.ne
  rw [setIntegral_const, smul_eq_mul, Measure.real, ← mul_assoc, inv_mul_cancel₀ hvpos.ne',
    one_mul]

theorem eamv2_core
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (G δ : ℝ) (hGpos : 0 < G) (hδpos : 0 < δ)
    (hfG : ∀ x y, |f x - f y| ≤ G * dist x y) :
    (∀ x ∈ K, |Extension K G δ f x - f x| ≤ 2 * δ * G) ∧
    (∀ x xπ : EuclideanSpace ℝ (Fin n), IsMetricProjection K x xπ →
      Extension K G δ f xπ ≤ Extension K G δ f x + 2 * δ * G) := by
  have hfc : Continuous f := by
    have : LipschitzWith (Real.toNNReal G) f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, Real.coe_toNNReal _ hGpos.le]
      exact hfG x y
    exact this.continuous
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => f y + G * Metric.infDist y K with hg
  have hgc : Continuous g := by
    rw [hg]; exact hfc.add (continuous_const.mul (Metric.continuous_infDist_pt K))
  have hcomp : ∀ z : EuclideanSpace ℝ (Fin n), Continuous (fun v => g (z + δ • v)) :=
    fun z => hgc.comp (by fun_prop)
  have hnv : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ‖δ • v‖ ≤ δ := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    nlinarith
  have hext : ∀ z, Extension K G δ f z =
      (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
        ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, g (z + δ • v) := by
    intro z; rfl
  refine ⟨?_, ?_⟩
  · intro x hx
    have hdist : ∀ v, dist (x + δ • v) x = ‖δ • v‖ := by
      intro v; rw [dist_eq_norm]; simp
    have hup : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        g (x + δ • v) ≤ (fun _ => f x) v + 2 * δ * G := by
      intro v hv
      have h1 := hfG (x + δ • v) x
      have h2 : Metric.infDist (x + δ • v) K ≤ ‖δ • v‖ := by
        rw [← hdist v]; exact Metric.infDist_le_dist_of_mem hx
      have h3 := hnv v hv
      rw [hdist] at h1
      simp only [hg]
      have := (abs_le.mp h1).2
      nlinarith
    have hlo : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        (fun _ => f x) v ≤ g (x + δ • v) + 2 * δ * G := by
      intro v hv
      have h1 := hfG (x + δ • v) x
      have h2 : 0 ≤ Metric.infDist (x + δ • v) K := Metric.infDist_nonneg
      have h3 := hnv v hv
      rw [hdist] at h1
      simp only [hg]
      have := (abs_le.mp h1).1
      nlinarith
    have A1 := eamv2_avg_le _ _ (hcomp x) continuous_const _ hup
    have A2 := eamv2_avg_le _ _ continuous_const (hcomp x) _ hlo
    rw [eamv2_avg_const] at A1 A2
    rw [hext x, abs_le]
    constructor <;> linarith
  · intro x xπ hπ
    obtain ⟨hxπK, hmin⟩ := hπ
    have hd : dist x xπ ≤ Metric.infDist x K :=
      (Metric.le_infDist hKne).mpr hmin
    have key : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        g (xπ + δ • v) ≤ g (x + δ • v) + 2 * δ * G := by
      intro v hv
      have h3 := hnv v hv
      have h1 := hfG (xπ + δ • v) (x + δ • v)
      have e1 : dist (xπ + δ • v) (x + δ • v) = dist x xπ := by
        rw [dist_add_right, dist_comm]
      rw [e1] at h1
      have h2 : Metric.infDist (xπ + δ • v) K ≤ ‖δ • v‖ := by
        have := Metric.infDist_le_dist_of_mem (x := xπ + δ • v) hxπK
        rw [dist_eq_norm] at this; simpa using this
      have h4 : Metric.infDist x K ≤ Metric.infDist (x + δ • v) K + ‖δ • v‖ := by
        have := Metric.infDist_le_infDist_add_dist (s := K) (x := x) (y := x + δ • v)
        rw [dist_eq_norm] at this; simpa using this
      simp only [hg]
      have := (abs_le.mp h1).2
      nlinarith
    have A := eamv2_avg_le _ _ (hcomp xπ) (hcomp x) _ key
    rw [hext xπ, hext x]
    exact A

end OnlineConvexOpt.OnlineBoosting

open OnlineConvexOpt.OnlineBoosting


theorem solution
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (G δ : ℝ) (hGpos : 0 < G) (hδpos : 0 < δ)
    (hfG : ∀ x y, |f x - f y| ≤ G * dist x y) :
    (∀ x ∈ K, |Extension K G δ f x - f x| ≤ 2 * δ * G) ∧
    (∀ x xπ : EuclideanSpace ℝ (Fin n), IsMetricProjection K x xπ →
      Extension K G δ f xπ ≤ Extension K G δ f x + 2 * δ * G) := by
  exact eamv2_core K hKconv hKne f hfconv G δ hGpos hδpos hfG
