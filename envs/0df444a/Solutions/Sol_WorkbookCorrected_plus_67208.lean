-- Prove2me | solution 1 for WorkbookCorrected.plus_67208
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:24:16.792629+00:00
-- url     : https://prove2.me/submissions/4d1d5950-4d1d-4062-929f-8202892ad577

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 14 2) ^ 2 = 8281 := by
  decide
