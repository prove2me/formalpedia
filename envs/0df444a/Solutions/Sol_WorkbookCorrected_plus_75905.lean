-- Prove2me | solution 1 for WorkbookCorrected.plus_75905
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:22:52.953397+00:00
-- url     : https://prove2.me/submissions/50a95cc2-0bd0-442f-9e6b-8eef7244da68

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 10 5) = 252 := by
  decide
