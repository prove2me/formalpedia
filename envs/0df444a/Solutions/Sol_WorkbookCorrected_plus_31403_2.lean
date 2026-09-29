-- Prove2me | solution 2 for WorkbookCorrected.plus_31403
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:43:58.289959+00:00
-- url     : https://prove2.me/submissions/1f230193-8088-4897-8348-35755bcc7a5c

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 32 5) - ((Nat.choose 6 1) * (Nat.choose 22 5)) + ((Nat.choose 6 2) * (Nat.choose 12 5)) = 55252 := by
  decide
