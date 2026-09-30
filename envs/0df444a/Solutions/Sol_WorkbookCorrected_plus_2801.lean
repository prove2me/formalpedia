-- Prove2me | solution 1 for WorkbookCorrected.plus_2801
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:31:09.578291+00:00
-- url     : https://prove2.me/submissions/15d87f0a-fc3d-451b-baf1-a1b99e41a238

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 7 2) < 6 * (Nat.choose 3 2) + 4 * (Nat.choose 2 2) := by
  decide
