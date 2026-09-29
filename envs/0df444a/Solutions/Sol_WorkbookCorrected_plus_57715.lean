-- Prove2me | solution 1 for WorkbookCorrected.plus_57715
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:15:52.733081+00:00
-- url     : https://prove2.me/submissions/4443ce03-7cff-4c17-a211-e2a7239ed14d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem solution : Real.pi - Real.pi = 0 := by
  exact sub_self Real.pi
