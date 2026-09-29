-- Prove2me | solution 1 for WorkbookCorrected.plus_29508
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:52:56.562881+00:00
-- url     : https://prove2.me/submissions/ac338992-131f-40ac-8730-136d8c8b07bb

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 6 3) = 20 := by
  decide
