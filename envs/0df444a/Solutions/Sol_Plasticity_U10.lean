-- Prove2me | solution 1 for Plasticity.U10
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:01:04.527582+00:00
-- url     : https://prove2.me/submissions/53b2d8ba-a3bf-4108-a2e1-9cbf80a67b7f

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Isometry
import Theorems.Thm_Plasticity_U16_norm_eq
import Theorems.Thm_Plasticity_U16_linearize
import Theorems.Thm_Plasticity_U16_complete

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [Nontrivial Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1)) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by
  have hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1 :=
    fun y hy => hsurj (Metric.sphere_subset_closedBall hy)
  have hnorm := (Plasticity.U16.norm_eq F hmaps hlip hsphere hcover).2
  obtain ⟨T, hT⟩ := Plasticity.U16.linearize F hmaps hlip hsphere hcover
  -- The range of T is closed and contains every point of the unit ball of Y.
  have hclosed : IsClosed (Set.range T) := T.isometry.isClosedEmbedding.isClosed_range
  have hball : ∀ y : Y, ‖y‖ ≤ 1 → y ∈ Set.range T := by
    intro y hy
    rw [← hclosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    set r : ℝ := min 1 (ε / 16) with hr
    have hr0 : 0 < r := lt_min one_pos (by positivity)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hry : r • y ∈ Metric.closedBall (0 : Y) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hr0.le]
      nlinarith [norm_nonneg y]
    obtain ⟨x, hx, hFx⟩ := hsurj hry
    have hxn : ‖x‖ ≤ r := by
      rw [← hnorm x hx, hFx, norm_smul, Real.norm_of_nonneg hr0.le]
      nlinarith [norm_nonneg y]
    have hTx : ‖r • y - T x‖ ≤ 8 * r ^ 2 := by
      have := hT x hx
      rw [hFx] at this
      nlinarith [norm_nonneg x]
    refine ⟨T (r⁻¹ • x), ⟨_, rfl⟩, ?_⟩
    have hrne : r ≠ 0 := hr0.ne'
    have hdist : dist y (T (r⁻¹ • x)) = r⁻¹ * ‖r • y - T x‖ := by
      have hv : y - T (r⁻¹ • x) = r⁻¹ • (r • y - T x) := by
        rw [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hrne, one_smul]
      rw [dist_eq_norm, hv, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr0).le]
    rw [hdist]
    calc r⁻¹ * ‖r • y - T x‖ ≤ r⁻¹ * (8 * r ^ 2) := by gcongr
      _ = 8 * r := by field_simp
      _ ≤ 8 * (ε / 16) := by gcongr; exact min_le_right _ _
      _ < ε := by linarith
  have hs : Function.Surjective T := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
      obtain ⟨x, hx⟩ := hball (‖y‖⁻¹ • y) (by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne'])
      refine ⟨‖y‖ • x, ?_⟩
      rw [map_smul, hx, smul_smul, mul_inv_cancel₀ hyn.ne', one_smul]
  let S : X ≃ₗᵢ[ℝ] Y := LinearIsometryEquiv.ofSurjective T hs
  have hS : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - S x‖ ≤ 8 * ‖x‖ ^ 2 := fun x hx => hT x hx
  exact ⟨S, Plasticity.U16.complete F hmaps hlip hsphere S 8 hS⟩
