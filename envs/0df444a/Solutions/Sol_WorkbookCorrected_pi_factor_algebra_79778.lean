-- Prove2me | solution 1 for WorkbookCorrected.pi_factor_algebra_79778
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:50:54.820617+00:00
-- url     : https://prove2.me/submissions/01b53dae-1475-4668-a83f-f79ff165ac6a

import Mathlib

theorem solution (a : ℝ) : a^2 * (1 - Real.pi / 4) = a^2 - a^2 * Real.pi / 4 := by
  ring
