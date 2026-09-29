-- Prove2me | solution 1 for WorkbookCorrected.plus_14320
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:14:36.95922+00:00
-- url     : https://prove2.me/submissions/7e61d9bc-3f8a-4dcb-8fe5-404f636abd2a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem solution : Real.tan (Real.pi / 4) = 1 := by
  exact Real.tan_pi_div_four
