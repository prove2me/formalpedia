-- Prove2me | solution 1 for WorkbookCorrected.plus_38483
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T19:34:40.243376+00:00
-- url     : https://prove2.me/submissions/16100690-ac12-41d2-9d2b-793a71ae1d35

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (10:ℚ) * ((Nat.choose 1 1) * (Nat.choose 9 4)) = (1:ℚ) * ((Nat.choose 10 1) * (Nat.choose 9 4)) := by
  norm_num
