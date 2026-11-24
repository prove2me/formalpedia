-- Prove2me | solution 1 for RoughSurfaceScattering.cone_below_interface
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:23:31.201814+00:00
-- url     : https://prove2.me/submissions/3dfe6eef-df2a-4468-9cde-476026950def

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory
open RoughSurfaceScattering

lemma abs_coord_le_norm (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

theorem solution (f : ℝ → ℝ) (s0 : ℝ) (hf : DifferentiableAt ℝ f s0) :
    ∃ r > (0 : ℝ), ∀ v : R2, v ≠ 0 → ‖v‖ < r →
      ‖v‖ ≤ 2 * @inner ℝ R2 _ v (normal f s0) → gpt f s0 + v ∈ Dminus f := by
  set d := deriv f s0 with hd
  set a := arcDen f s0 with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  -- first-order Taylor bound with error `(a/4)|h|`
  have hlo := hf.hasDerivAt.isLittleO
  have hev := hlo.def (c := a / 4) (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, fun v hv0 hvr hcone => ?_⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  -- the inner product with the normal
  have hinner : @inner ℝ R2 _ v (normal f s0) = a⁻¹ * (d * v 0 - v 1) := by
    simp [normal, pt, ← ha, ← hd, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_right]
    ring_nf
    try simp
  rw [hinner] at hcone
  have hkey : a * ‖v‖ ≤ 2 * (d * v 0 - v 1) := by
    have := mul_le_mul_of_nonneg_left hcone hapos.le
    calc a * ‖v‖ ≤ a * (2 * (a⁻¹ * (d * v 0 - v 1))) := this
      _ = 2 * (d * v 0 - v 1) := by field_simp
  have h0 := abs_coord_le_norm v 0
  have hdist : dist (s0 + v 0) s0 < r := by
    rw [Real.dist_eq, add_sub_cancel_left]; linarith
  have htay := hball hdist
  simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul] at htay
  have hlow : f s0 + v 0 * d - a / 4 * |v 0| ≤ f (s0 + v 0) := by
    have := (abs_le.mp htay).1
    linarith
  show (gpt f s0 + v) 1 < f ((gpt f s0 + v) 0)
  simp only [gpt, pt, PiLp.add_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have : a / 4 * |v 0| ≤ a / 4 * ‖v‖ := mul_le_mul_of_nonneg_left h0 (by positivity)
  nlinarith
