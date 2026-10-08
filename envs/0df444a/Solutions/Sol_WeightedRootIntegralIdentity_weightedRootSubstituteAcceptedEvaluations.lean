-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootSubstituteAcceptedEvaluations
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T06:44:08.582228+00:00
-- url     : https://prove2.me/submissions/81a95dcf-e719-4601-beb7-4f7682cb4781

import Mathlib

theorem solution
    (J d p : ℂ) (S P : ℝ)
    (hbalance : J = 2 * Real.pi * Complex.I * (-(d.re : ℂ) + (p.re : ℂ)))
    (hd : d.re = -S)
    (hp : p.re = -P) :
    J = 2 * Real.pi * Complex.I * (((S - P : ℝ) : ℂ)) := by
  rw [hd, hp] at hbalance
  simpa [sub_eq_add_neg] using hbalance
