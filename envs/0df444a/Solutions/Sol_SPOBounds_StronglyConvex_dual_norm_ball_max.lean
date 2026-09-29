-- Prove2me | solution 1 for SPOBounds.StronglyConvex.dual_norm_ball_max
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:30.702449+00:00
-- url     : https://prove2.me/submissions/abcac857-564e-4234-a787-ffc417b461d9

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (c : StrongDual ℝ E) (what : E) {r : ℝ} (hr : 0 ≤ r) :
    IsGreatest ((fun v => c v) '' Metric.closedBall what r) (c what + r * ‖c‖) := by
  obtain ⟨x0, hx0, hmax⟩ : ∃ x ∈ Metric.closedBall (0 : E) 1,
      IsMaxOn (fun v => c v) (Metric.closedBall (0 : E) 1) x :=
    (isCompact_closedBall (0 : E) 1).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩ c.continuous.continuousOn
  have hmax' : ∀ v ∈ Metric.closedBall (0 : E) 1, c v ≤ c x0 := fun v hv => hmax hv
  have hx0n : ‖x0‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx0
  have h0 : (0 : ℝ) ≤ c x0 := by
    have := hmax' 0 (Metric.mem_closedBall_self zero_le_one)
    simpa using this
  have hcn : ‖c‖ = c x0 := by
    refine le_antisymm (c.opNorm_le_bound h0 ?_) ?_
    · intro v
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hvn]
          field_simp
        have hmem : ((‖v‖⁻¹ : ℝ) • v) ∈ Metric.closedBall (0 : E) 1 := by
          simp [Metric.mem_closedBall, dist_zero_right, hu]
        have hmem2 : (-((‖v‖⁻¹ : ℝ) • v)) ∈ Metric.closedBall (0 : E) 1 := by
          simp [Metric.mem_closedBall, dist_zero_right, hu]
        have h1 := hmax' _ hmem
        have h2 := hmax' _ hmem2
        simp only [map_smul, map_neg, smul_eq_mul] at h1 h2
        have hmul1 : ‖v‖ * (‖v‖⁻¹ * c v) ≤ ‖v‖ * c x0 :=
          mul_le_mul_of_nonneg_left h1 hvn.le
        have hmul2 : ‖v‖ * (-(‖v‖⁻¹ * c v)) ≤ ‖v‖ * c x0 :=
          mul_le_mul_of_nonneg_left h2 hvn.le
        rw [show ‖v‖ * (‖v‖⁻¹ * c v) = c v by field_simp] at hmul1
        rw [show ‖v‖ * (-(‖v‖⁻¹ * c v)) = -(c v) by field_simp] at hmul2
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith
    · calc (c x0 : ℝ) ≤ ‖c x0‖ := le_abs_self _
        _ ≤ ‖c‖ * ‖x0‖ := c.le_opNorm x0
        _ ≤ ‖c‖ * 1 := by gcongr
        _ = ‖c‖ := mul_one _
  constructor
  · refine ⟨what + r • x0, ?_, ?_⟩
    · simp only [Metric.mem_closedBall, dist_eq_norm]
      calc ‖what + r • x0 - what‖ = r * ‖x0‖ := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
        _ ≤ r * 1 := by gcongr
        _ = r := mul_one r
    · simp only [map_add, map_smul, smul_eq_mul, hcn]
  · rintro z ⟨v, hv, rfl⟩
    simp only [Metric.mem_closedBall, dist_eq_norm] at hv
    have h1 : c v = c what + c (v - what) := by rw [map_sub]; ring
    have h2 : c (v - what) ≤ ‖c‖ * ‖v - what‖ :=
      le_trans (le_abs_self _) (c.le_opNorm _)
    have h3 : ‖c‖ * ‖v - what‖ ≤ ‖c‖ * r := by gcongr
    simp only
    rw [h1]
    linarith
