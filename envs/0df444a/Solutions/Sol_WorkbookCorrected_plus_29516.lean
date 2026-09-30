-- Prove2me | solution 1 for WorkbookCorrected.plus_29516
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T14:31:04.421001+00:00
-- url     : https://prove2.me/submissions/91f09cf7-57d9-474d-9f16-cc77c959da48

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 2 2) = 1) ∧ ((Nat.choose 3 3) = 1) := by
  decide
