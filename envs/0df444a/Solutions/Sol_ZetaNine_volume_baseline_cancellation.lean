-- Prove2me | solution 1 for ZetaNine.volume_baseline_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-24T14:10:17.089627+00:00
-- url     : https://prove2.me/submissions/7f240a46-92e3-471a-9f55-bc4361652ef3

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution
    (D s N g Δ Ξ : ℝ)
    (hD : 0 < D) (hs : 0 < s) (hN : 0 < N) (hg : 0 < g)
    (hΞ : 0 < Ξ)
    (harea : Δ = (s ^ 2 * N / D ^ 2) * Ξ) :
    Real.log (D / s) + (1 / 2 : ℝ) * Real.log Δ -
        (1 / 2 : ℝ) * Real.log g =
      (Real.log Ξ + Real.log (N / g)) / 2 := by
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hΞ0 : Ξ ≠ 0 := ne_of_gt hΞ
  have hs20 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  have hD20 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD0
  have hnum0 : s ^ 2 * N ≠ 0 := mul_ne_zero hs20 hN0
  have hquot0 : s ^ 2 * N / D ^ 2 ≠ 0 := div_ne_zero hnum0 hD20
  have hlogarea : Real.log Δ =
      2 * Real.log s + Real.log N - 2 * Real.log D + Real.log Ξ := by
    rw [harea, Real.log_mul hquot0 hΞ0,
      Real.log_div hnum0 hD20, Real.log_mul hs20 hN0,
      Real.log_pow, Real.log_pow]
    ring
  rw [Real.log_div hD0 hs0, hlogarea, Real.log_div hN0 hg0]
  ring
