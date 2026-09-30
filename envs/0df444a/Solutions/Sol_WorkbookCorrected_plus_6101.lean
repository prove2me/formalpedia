-- Prove2me | solution 1 for WorkbookCorrected.plus_6101
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:15:19.831974+00:00
-- url     : https://prove2.me/submissions/2400bde3-de60-4810-9f43-4a5cb0b98b96

import Mathlib.Tactic

theorem solution : ((Nat.factorial 7))/((Nat.factorial 3)*(Nat.factorial 2)*(Nat.factorial 2)) = 210 := by
  norm_num [Nat.factorial]
