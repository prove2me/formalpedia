-- Prove2me | solution 1 for WorkbookCorrected.plus_246
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:15:19.023994+00:00
-- url     : https://prove2.me/submissions/b4d027c5-f705-49fe-b1ba-a94c1cd18c8f

import Mathlib.Tactic

theorem solution : (Nat.choose (4+218-1) 218) = 1774630 := by
  change Nat.choose 221 218=1774630
  rw [Nat.choose_symm_of_eq_add (show 221=218+3 by norm_num)]
  have h:=Nat.choose_succ_right_eq 221 2
  norm_num [Nat.choose_two_right] at h
  omega
