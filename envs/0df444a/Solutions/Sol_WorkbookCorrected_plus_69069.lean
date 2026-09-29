-- Prove2me | solution 1 for WorkbookCorrected.plus_69069
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:25:14.36235+00:00
-- url     : https://prove2.me/submissions/19180f48-ddc9-4973-b35e-140abbfb5e50

import Mathlib.Data.Nat.Choose.Basic

theorem solution : 4 ^ 6 - (Nat.choose 4 3 * 3 ^ 6) + (Nat.choose 4 2 * 2 ^ 6) - (Nat.choose 4 1 * 1 ^ 6) = 1560 := by
  decide
