-- Prove2me | solution 1 for WorkbookCorrected.plus_79983
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T18:28:05.443263+00:00
-- url     : https://prove2.me/submissions/3cb615e0-d028-4d24-ab1b-a33216637977

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ ((Nat.factorial 8) / ((Nat.factorial 2)^4) = 90) := by
  decide
