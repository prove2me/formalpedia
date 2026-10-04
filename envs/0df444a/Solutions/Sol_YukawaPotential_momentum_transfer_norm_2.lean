-- Prove2me | solution 2 for YukawaPotential.momentum_transfer_norm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T18:16:07.89102+00:00
-- url     : https://prove2.me/submissions/c061aa40-495c-4ca0-9663-0ad2e8693992

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open InnerProductGeometry

theorem solution (p : ℝ) (P P' : EuclideanSpace ℝ (Fin 3))
    (hP : ‖P‖ = p) (hP' : ‖P'‖ = p) :
    ‖P - P'‖ = 2 * p * Real.sin (angle P P' / 2) := by
  set θ : ℝ := angle P P' with hθ
  have hθ0 : 0 ≤ θ := by simpa [hθ] using angle_nonneg P P'
  have hθpi : θ ≤ Real.pi := by simpa [hθ] using angle_le_pi P P'
  have hhalf0 : 0 ≤ θ / 2 := div_nonneg hθ0 (by norm_num)
  have hhalfpi : θ / 2 ≤ Real.pi := by
    calc
      θ / 2 ≤ θ := div_le_self hθ0 (by norm_num)
      _ ≤ Real.pi := hθpi
  have hsin : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 hhalfpi
  have hp : 0 ≤ p := by rw [← hP]; exact norm_nonneg P
  have hsq : ‖P - P'‖ ^ 2 = (2 * p * Real.sin (θ / 2)) ^ 2 := by
    have hlaw :=
      norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle P P'
    have hhalf : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have hsum : θ / 2 + θ / 2 = θ := by ring
      have hcs : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 :=
        Real.cos_sq_add_sin_sq (θ / 2)
      have hcos2 :
          Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 =
            1 - 2 * Real.sin (θ / 2) ^ 2 := by
        have hcos1 : Real.cos (θ / 2) ^ 2 = 1 - Real.sin (θ / 2) ^ 2 := by
          linarith [hcs]
        linarith [hcos1]
      calc
        Real.cos θ = Real.cos (θ / 2 + θ / 2) := by rw [hsum]
        _ = Real.cos (θ / 2) * Real.cos (θ / 2) -
              Real.sin (θ / 2) * Real.sin (θ / 2) := by
          rw [Real.cos_add]
        _ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by ring
        _ = 1 - 2 * Real.sin (θ / 2) ^ 2 := hcos2
    have hpow : ‖P - P'‖ ^ 2 = p ^ 2 + p ^ 2 - 2 * p * p * Real.cos θ := by
      simpa [sq, hP, hP', hθ] using hlaw
    rw [hpow, hhalf]
    ring
  have hR : 0 ≤ 2 * p * Real.sin (θ / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hp) hsin
  have hL : 0 ≤ ‖P - P'‖ := norm_nonneg _
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · exact h
  · have hneg : ‖P - P'‖ ≤ 0 := by
      rw [h]
      exact neg_nonpos.mpr hR
    have hzero : ‖P - P'‖ = 0 := le_antisymm hneg hL
    have hR0 : 2 * p * Real.sin (θ / 2) = 0 := by linarith
    rw [hzero, hR0]
