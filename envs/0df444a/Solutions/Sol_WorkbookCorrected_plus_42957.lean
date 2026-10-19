-- Prove2me | solution 1 for WorkbookCorrected.plus_42957
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-19T12:23:11.168065+00:00
-- url     : https://prove2.me/submissions/e95bf448-470e-4215-afe6-ed69ac65a17d

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (((Nat.choose 6 0) - (Nat.choose 6 11)) + ((Nat.choose 6 1) - (Nat.choose 6 7)) + ((Nat.choose 6 2) - (Nat.choose 6 3)) = 2) := by
  decide
