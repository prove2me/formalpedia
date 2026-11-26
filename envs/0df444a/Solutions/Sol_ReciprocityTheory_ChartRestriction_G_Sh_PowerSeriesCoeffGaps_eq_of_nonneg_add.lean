-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.eq_of_nonneg_add
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:30:05.841443+00:00
-- url     : https://prove2.me/submissions/2bacc8ef-98d6-4ea6-8f73-1829ed0e908d

import Mathlib

variable {K : Type*} [Field K] {v : AddValuation K (WithTop ℝ)}

private lemma add_eq_of_lt {x y : K} {A B : ℝ}
    (hx : v x = A) (hy : v y = B) (h : A < B) : v (x + y) = A := by
  have hlt : v x < v y := by
    rw [hx, hy]
    exact WithTop.coe_lt_coe.mpr h
  rw [AddValuation.map_add_eq_of_lt_left v hlt, hx]

theorem solution {x y : K} {A B : ℝ} (hA : A < 0) (hx : v x = A) (hy : v y = B)
    (h : 0 ≤ v (x + y)) : A = B := by
  rcases lt_trichotomy A B with hlt | rfl | hgt
  · have : v (x + y) = A := add_eq_of_lt hx hy hlt
    rw [this] at h
    have : (0 : ℝ) ≤ A := WithTop.coe_le_coe.mp (by exact_mod_cast h)
    linarith
  · rfl
  · have : v (y + x) = B := add_eq_of_lt (x := y) (y := x) hy hx hgt
    rw [add_comm x y, this] at h
    have hB : (0 : ℝ) ≤ B := WithTop.coe_le_coe.mp (by exact_mod_cast h)
    linarith
