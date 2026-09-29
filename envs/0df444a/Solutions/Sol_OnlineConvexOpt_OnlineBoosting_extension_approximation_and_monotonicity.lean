-- Prove2me | solution 1 for OnlineConvexOpt.OnlineBoosting.extension_approximation_and_monotonicity
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:11:55.861978+00:00
-- url     : https://prove2.me/submissions/37fb2d79-239f-4360-9a5e-650426d9b467

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Extension
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.OnlineBoosting

open MeasureTheory Filter Topology

/-- The indicator function of the origin in `ℝ¹`. -/
noncomputable def aux_eam_f : EuclideanSpace ℝ (Fin 1) → ℝ :=
  Set.indicator ({0} : Set (EuclideanSpace ℝ (Fin 1))) (fun _ => 1)

lemma aux_eam_f_zero : aux_eam_f 0 = 1 := by
  simp [aux_eam_f]

lemma aux_eam_f_ne {y : EuclideanSpace ℝ (Fin 1)} (hy : y ≠ 0) : aux_eam_f y = 0 := by
  simp [aux_eam_f, hy]

lemma aux_eam_grad : ∀ x, ∀ v, HasGradientAt aux_eam_f v x → ‖v‖ ≤ 1 := by
  intro x v h
  by_cases hx : x = 0
  · exfalso
    subst hx
    have hc : Tendsto aux_eam_f (𝓝[≠] (0 : EuclideanSpace ℝ (Fin 1))) (𝓝 1) := by
      have := h.continuousAt
      rw [ContinuousAt, aux_eam_f_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h0 : Tendsto aux_eam_f (𝓝[≠] (0 : EuclideanSpace ℝ (Fin 1))) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (aux_eam_f_ne hy).symm
    have := tendsto_nhds_unique hc h0
    norm_num at this
  · have heq : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] aux_eam_f := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      exact (aux_eam_f_ne hy).symm
    have h2 : HasGradientAt (fun _ => (0 : ℝ)) v x := h.congr_of_eventuallyEq heq
    have h3 : HasGradientAt (fun _ => (0 : ℝ)) 0 x := hasGradientAt_const x 0
    rw [h2.unique h3]
    simp

lemma aux_eam_ext0 :
    Extension (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) 1 (1/2) aux_eam_f 0 = 0 := by
  unfold Extension SmoothedFunction
  have hint : ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
      (aux_eam_f (0 + (1/2 : ℝ) • v) + 1 * Metric.infDist (0 + (1/2 : ℝ) • v)
        (Set.univ : Set (EuclideanSpace ℝ (Fin 1)))) = 0 := by
    apply integral_eq_zero_of_ae
    apply ae_restrict_of_ae
    have hs : volume ({0} : Set (EuclideanSpace ℝ (Fin 1))) = 0 := measure_singleton 0
    have hae : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))), v ≠ 0 := by
      rw [ae_iff]
      simp [hs]
    filter_upwards [hae] with v hv
    have hv' : (0 : EuclideanSpace ℝ (Fin 1)) + (1/2 : ℝ) • v ≠ 0 := by
      rw [zero_add]
      exact smul_ne_zero (by norm_num) hv
    simp only [Pi.zero_apply]
    rw [aux_eam_f_ne hv', Metric.infDist_zero_of_mem (Set.mem_univ _)]
    simp
  rw [hint, mul_zero]

end OnlineConvexOpt.OnlineBoosting

open OnlineConvexOpt.OnlineBoosting

theorem solution : ¬ (∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G δ : ℝ) (hGpos : 0 < G) (hδpos : 0 < δ)
    (hfG : ∀ x, ∀ v, HasGradientAt f v x → ‖v‖ ≤ G),
    (∀ x ∈ K, |Extension K G δ f x - f x| ≤ δ * G) ∧
    (∀ x xπ : EuclideanSpace ℝ (Fin n), IsMetricProjection K x xπ →
      Extension K G δ f xπ ≤ Extension K G δ f x + δ * G)) := by
  intro h
  have := (h (n := 1) Set.univ convex_univ Set.univ_nonempty aux_eam_f 1 (1/2) one_pos
    (by norm_num) aux_eam_grad).1 0 (Set.mem_univ _)
  rw [aux_eam_ext0, aux_eam_f_zero] at this
  norm_num at this
