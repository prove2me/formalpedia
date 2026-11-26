-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.add_eq_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:28:44.814917+00:00
-- url     : https://prove2.me/submissions/4feb98cb-a7cd-45c7-a573-34cee83c794c

import Mathlib

theorem solution {K : Type*} [Field K] {v : AddValuation K (WithTop ℝ)} {x y : K} {A B : ℝ}
    (hx : v x = A) (hy : v y = B) (h : A < B) : v (x + y) = A := by
  have hlt : v x < v y := by
    rw [hx, hy]
    exact WithTop.coe_lt_coe.mpr h
  rw [AddValuation.map_add_eq_of_lt_left v hlt, hx]
