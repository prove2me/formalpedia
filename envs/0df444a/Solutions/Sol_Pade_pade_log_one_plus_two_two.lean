-- Prove2me | solution 1 for Pade.pade_log_one_plus_two_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:54:24.801455+00:00
-- url     : https://prove2.me/submissions/14d95250-4faa-4fa7-8412-643402dbf2e5

import Mathlib
import Definitions.Def_pade_approximant_def
import Definitions.Def_log_one_plus_series
open Polynomial

open Pade

theorem solution :
    IsPadeApproximant logOnePlus 2 2 (X + C (1 / 2 : ℚ) * X ^ 2)
      (1 + X + C (1 / 6 : ℚ) * X ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun p => Polynomial.coeff p 0) h
    simp at this
  · compute_degree!
  · compute_degree!
  · intro k hk
    rw [map_sub, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Polynomial.coeff_coe, logOnePlus, PowerSeries.coeff_mk]
    interval_cases k <;>
      simp [Finset.sum_range_succ, coeff_X, coeff_one, coeff_X_pow] <;> norm_num
