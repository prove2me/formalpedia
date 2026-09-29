-- Prove2me | solution 1 for WorkbookCorrected.plus_79038
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:27.229318+00:00
-- url     : https://prove2.me/submissions/ff78824d-44a9-438c-b076-eb35dc512e46

import Mathlib.Data.Nat.Factorial.Basic

theorem solution : Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2) = 180 := by
  decide
