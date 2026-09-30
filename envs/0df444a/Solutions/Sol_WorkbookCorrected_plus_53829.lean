-- Prove2me | solution 1 for WorkbookCorrected.plus_53829
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T11:15:21.309836+00:00
-- url     : https://prove2.me/submissions/bfadd14e-3909-4902-a173-85fca68e7a9d

import Mathlib.Tactic

theorem solution : ¬ ((Nat.factorial 9) / ((Nat.factorial 4) * (Nat.factorial 2)) = 90) := by
  norm_num [Nat.factorial]
