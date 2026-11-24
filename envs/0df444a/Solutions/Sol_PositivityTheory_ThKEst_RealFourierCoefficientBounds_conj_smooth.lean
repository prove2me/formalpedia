-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.conj_smooth
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:55:50.040801+00:00
-- url     : https://prove2.me/submissions/c058d688-ca66-457f-8623-aa3f0e779f48

import Mathlib
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]


theorem solution (f : SchwartzMap V ℂ) : ContDiff ℝ ∞ fun u => (starRingEnd ℂ) (f u) := by
  exact Complex.conjCLE.contDiff.comp (f.smooth _)
