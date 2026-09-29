-- Prove2me | solution 1 for Pade.pade_exp_five_five
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:54:12.23677+00:00
-- url     : https://prove2.me/submissions/7f933b8a-3328-4330-be02-aa4d505fc3b6

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

open Pade

theorem solution :
    IsPadeApproximant (PowerSeries.exp ℚ) 5 5
      (1 + C (1 / 2 : ℚ) * X + C (1 / 9 : ℚ) * X ^ 2 + C (1 / 72 : ℚ) * X ^ 3
        + C (1 / 1008 : ℚ) * X ^ 4 + C (1 / 30240 : ℚ) * X ^ 5)
      (1 - C (1 / 2 : ℚ) * X + C (1 / 9 : ℚ) * X ^ 2 - C (1 / 72 : ℚ) * X ^ 3
        + C (1 / 1008 : ℚ) * X ^ 4 - C (1 / 30240 : ℚ) * X ^ 5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun p => Polynomial.coeff p 0) h
    simp at this
  · compute_degree!
  · compute_degree!
  · intro k hk
    rw [map_sub, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Polynomial.coeff_coe, PowerSeries.coeff_exp]
    interval_cases k <;>
      simp [Finset.sum_range_succ, coeff_X, coeff_one, coeff_X_pow, Nat.factorial] <;> norm_num
