-- Prove2me | solution 1 for WorkbookCorrected.plus_3655
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T09:17:49.652987+00:00
-- url     : https://prove2.me/submissions/1557ab1f-5f3d-424d-8ec1-488023f6c49a

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 10 4) < (Nat.choose 10 5)) = True := by
  decide
