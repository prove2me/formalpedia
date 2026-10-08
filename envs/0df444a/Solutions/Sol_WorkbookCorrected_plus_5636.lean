-- Prove2me | solution 1 for WorkbookCorrected.plus_5636
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T20:57:01.83217+00:00
-- url     : https://prove2.me/submissions/88335fa1-bfbd-471c-ab20-62363c1cf21b

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 10 2) * 2 ^ 8 = 11520 := by
  decide
