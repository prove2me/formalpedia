-- Prove2me | solution 1 for WorkbookCorrected.plus_20267
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:58:14.503604+00:00
-- url     : https://prove2.me/submissions/cda68dbd-bb24-40af-96f3-d059fd62343f

import Mathlib.Tactic.NormNum

theorem solution : (2 ^ 64) ≤ (Nat.factorial 64) := by
  decide
