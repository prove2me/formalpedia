-- Prove2me | solution 1 for PrivInfoHier.Main.eq_B_4_small_delta
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T16:17:26.723389+00:00
-- url     : https://prove2.me/submissions/0eab3a6c-b14f-44e4-8824-afebc1f44d25

import Mathlib

set_option autoImplicit false

/-- A small-`δ` form of the `exp 1` boundary inequality: the ratio `(1-θ)/θ` is controlled by
`1 / log(1/(1-θ))`. -/
theorem solution (θ δ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 - 1 / Real.exp 1) :
    ((1 - θ) / θ) * ((Real.exp 1 - 1) / Real.exp 1 - δ) ≤
      (1 - δ - 1 / Real.exp 1) / Real.log (1 / (1 - θ)) := by
  have hApos : 0 < 1 - θ := by linarith
  have hLpos : 0 < Real.log (1 / (1 - θ)) := by
    apply Real.log_pos
    rw [one_div]
    exact (one_lt_inv₀ hApos).mpr (by linarith : 1 - θ < 1)
  have hlog_le : Real.log (1 / (1 - θ)) ≤ θ / (1 - θ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / (1 - θ))
    have hsimp : 1 / (1 - θ) - 1 = θ / (1 - θ) := by
      field_simp
      ring
    linarith
  have hmul : ((1 - θ) / θ) * Real.log (1 / (1 - θ)) ≤ 1 := by
    calc ((1 - θ) / θ) * Real.log (1 / (1 - θ))
        ≤ ((1 - θ) / θ) * (θ / (1 - θ)) :=
          mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = 1 := by
          field_simp
  have hK : 0 ≤ (Real.exp 1 - 1) / Real.exp 1 - δ := by
    have h1 : (Real.exp 1 - 1) / Real.exp 1 = 1 - 1 / Real.exp 1 := by
      field_simp
    rw [h1]
    linarith
  have hRHS : 1 - δ - 1 / Real.exp 1 = (Real.exp 1 - 1) / Real.exp 1 - δ := by
    have h1 : (Real.exp 1 - 1) / Real.exp 1 = 1 - 1 / Real.exp 1 := by
      field_simp
    rw [h1]
    ring
  rw [hRHS, le_div_iff₀ hLpos]
  calc ((1 - θ) / θ) * ((Real.exp 1 - 1) / Real.exp 1 - δ) * Real.log (1 / (1 - θ))
      = (((1 - θ) / θ) * Real.log (1 / (1 - θ))) * ((Real.exp 1 - 1) / Real.exp 1 - δ) := by
        ring
    _ ≤ 1 * ((Real.exp 1 - 1) / Real.exp 1 - δ) := mul_le_mul_of_nonneg_right hmul hK
    _ = (Real.exp 1 - 1) / Real.exp 1 - δ := one_mul _
