-- Prove2me | solution 1 for WorkbookCorrected.plus_50821
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:23:48.067561+00:00
-- url     : https://prove2.me/submissions/f570cafc-84c0-4016-b301-e28f6239c38e

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 14 5) = 2002 := by
  decide
