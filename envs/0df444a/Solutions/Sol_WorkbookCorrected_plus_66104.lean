-- Prove2me | solution 1 for WorkbookCorrected.plus_66104
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:14:42.804954+00:00
-- url     : https://prove2.me/submissions/80b1847a-318d-4ea7-ab4a-fefe1a80bac1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem solution : Real.cos (Real.pi / 2) = 0 := by
  exact Real.cos_pi_div_two
