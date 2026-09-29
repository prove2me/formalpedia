-- Prove2me | solution 1 for WorkbookCorrected.plus_12215
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:14:36.353426+00:00
-- url     : https://prove2.me/submissions/67ff31d4-65be-41b5-b53e-bf61c19a71f2

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem solution : Real.sin (Real.pi / 2) = 1 := by
  exact Real.sin_pi_div_two
