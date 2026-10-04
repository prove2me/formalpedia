-- Prove2me | solution 1 for YukawaPotential.momentum_transfer_norm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T17:50:20.43313+00:00
-- url     : https://prove2.me/submissions/c1f5988a-5724-49e9-8101-fd74b0dd3b1c

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

open YukawaPotential in
theorem solution (p : ℝ) (P P' : EuclideanSpace ℝ (Fin 3))
    (hP : ‖P‖ = p) (hP' : ‖P'‖ = p) :
    ‖P - P'‖ = 2 * p * Real.sin (InnerProductGeometry.angle P P' / 2) := by
  have hp : 0 ≤ p := hP ▸ norm_nonneg _
  have h0 := InnerProductGeometry.angle_nonneg P P'
  have h1 := InnerProductGeometry.angle_le_pi P P'
  set θ := InnerProductGeometry.angle P P' with hθ
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have e : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [e, Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have key :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle P P'
  rw [hP, hP', hc] at key
  have hn : 0 ≤ 2 * p * Real.sin (θ / 2) := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (P - P')), ← Real.sqrt_sq hn]
  congr 1
  linear_combination key
