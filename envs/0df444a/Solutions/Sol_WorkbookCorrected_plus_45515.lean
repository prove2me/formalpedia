-- Prove2me | solution 1 for WorkbookCorrected.plus_45515
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T11:15:20.580234+00:00
-- url     : https://prove2.me/submissions/c16ef002-59d4-4598-83e1-1105e558b038

import Mathlib.Tactic

theorem solution : ¬ ((Nat.factorial 10) / ((Nat.factorial 2) ^ 3) = 45000) := by
  norm_num [Nat.factorial]
