-- Prove2me | solution 1 for WorkbookCorrected.plus_26796
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T20:56:38.323694+00:00
-- url     : https://prove2.me/submissions/a037e4fd-b983-48f8-8169-09ba5645e98f

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 12 5)) - ((Nat.choose 10 3)) = 672 := by
  decide
