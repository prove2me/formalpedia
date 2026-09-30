-- Prove2me | solution 2 for WorkbookCorrected.plus_3655
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:20:25.192317+00:00
-- url     : https://prove2.me/submissions/0ac37f01-f4a7-4b09-9266-faac8cd3ba4f

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 10 4) < (Nat.choose 10 5)) = True := by decide
