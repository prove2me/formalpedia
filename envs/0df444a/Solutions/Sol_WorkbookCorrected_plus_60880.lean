-- Prove2me | solution 1 for WorkbookCorrected.plus_60880
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:22:52.690444+00:00
-- url     : https://prove2.me/submissions/b697540d-2ce1-4c15-8248-ba745103761c

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 7 2 * (Nat.choose 16 1)) = 336 := by
  decide
