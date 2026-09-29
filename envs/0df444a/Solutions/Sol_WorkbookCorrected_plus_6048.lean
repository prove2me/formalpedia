-- Prove2me | solution 1 for WorkbookCorrected.plus_6048
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:45:39.663612+00:00
-- url     : https://prove2.me/submissions/ac1723ff-c98d-4ee8-8133-177dd23c42cc

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 64 2) = 2016 := by
  decide
