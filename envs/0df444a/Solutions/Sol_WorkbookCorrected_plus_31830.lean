-- Prove2me | solution 1 for WorkbookCorrected.plus_31830
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T12:48:36.717443+00:00
-- url     : https://prove2.me/submissions/75bf62c1-69c2-4931-9b9b-b9f92e14c942

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose (6 + 4 - 1) 4) = 126 := by
  decide
