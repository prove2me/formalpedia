-- Prove2me | solution 1 for WorkbookCorrected.plus_49544
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:53:06.766408+00:00
-- url     : https://prove2.me/submissions/17492845-6bf9-4bc2-9570-97816a4f2433

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 3 1) * ((Nat.choose 5 2) + (Nat.choose 5 3)) * (Nat.choose 4 2) = 360 := by
  decide
