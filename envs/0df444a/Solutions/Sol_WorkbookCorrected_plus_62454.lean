-- Prove2me | solution 1 for WorkbookCorrected.plus_62454
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T14:35:24.554114+00:00
-- url     : https://prove2.me/submissions/9bb83435-8990-46f8-9891-559d0bbae0ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : 77  ^  10 ≥ 2  ^  10 * ((Nat.factorial 10))  ^  2 := by
  decide
