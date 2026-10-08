-- Prove2me | solution 1 for RhinViola.unitIntervalMonomialIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:48:14.213274+00:00
-- url     : https://prove2.me/submissions/1cda09ca-3060-4a59-a201-27dc5dedd1e4

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

theorem solution (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ n) =
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
  rw [integral_pow] <;> norm_num
