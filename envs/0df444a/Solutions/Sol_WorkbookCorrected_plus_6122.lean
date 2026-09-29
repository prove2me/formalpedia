-- Prove2me | solution 1 for WorkbookCorrected.plus_6122
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:52.168516+00:00
-- url     : https://prove2.me/submissions/f7ffcc30-4495-4b27-bffc-db621b617ced

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.choose 16 4 - Nat.choose 14 4 = 819 := by
  decide
