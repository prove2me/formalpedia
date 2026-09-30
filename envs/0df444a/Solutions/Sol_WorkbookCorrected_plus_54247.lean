-- Prove2me | solution 1 for WorkbookCorrected.plus_54247
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T11:15:22.087144+00:00
-- url     : https://prove2.me/submissions/5b1b8985-5aa1-485b-bc7a-b66ef19e471d

import Mathlib.Tactic

theorem solution : ¬ (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 1) := by
  norm_num [Nat.factorial]
