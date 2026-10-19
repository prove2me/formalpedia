-- Prove2me | solution 1 for WorkbookCorrected.plus_32884
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-19T12:23:04.083206+00:00
-- url     : https://prove2.me/submissions/d81922dc-13c4-4d4c-89c2-754cbbb974ba

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (((Nat.choose 24 0) - (Nat.choose 24 2) + (Nat.choose 24 4) - (Nat.choose 24 6) + (Nat.choose 24 8) - (Nat.choose 24 10) + (Nat.choose 24 12) - (Nat.choose 24 14) + (Nat.choose 24 16) - (Nat.choose 24 18) + (Nat.choose 24 20) - (Nat.choose 24 22) + (Nat.choose 24 24)) = 4096) := by
  decide +kernel
