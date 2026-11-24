-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.shift_smooth
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:55:39.674979+00:00
-- url     : https://prove2.me/submissions/ed4bb6b9-9f4c-4bfd-971e-9bc0424bc3e9

import Mathlib
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]


theorem solution (f : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ fun u => f (u + x) := by
  exact (f.smooth _).comp (contDiff_id.add contDiff_const)
