-- Prove2me | solution 1 for Underdogs.odds_lt_odds
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T14:20:28.005208+00:00
-- url     : https://prove2.me/submissions/5450644e-5c3a-46eb-b170-724cb14e5b8a

import Mathlib

theorem solution (x y : ℝ) (hyx : y < x) (hx : x < 1) :
    y / (1 - y) < x / (1 - x) := by
  have hy1 : 0 < 1 - y := by linarith
  have hx1 : 0 < 1 - x := by linarith
  rw [div_lt_div_iff₀ hy1 hx1]
  nlinarith
