-- Prove2me | solution 1 for WorkbookCorrected.plus_77227
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-22T18:28:05.544347+00:00
-- url     : https://prove2.me/submissions/c6985c49-c5b5-4e3d-8b7a-4016c49c3370

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ ((Nat.factorial 6)/((Nat.factorial 2)*(Nat.factorial 2)) = 90) := by
  decide
