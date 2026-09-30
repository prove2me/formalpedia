-- Prove2me | solution 1 for WorkbookCorrected.plus_26043
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T19:19:09.006607+00:00
-- url     : https://prove2.me/submissions/aac1908a-5c03-4d63-bc9e-a3d59a500244

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose (15-1) (3-1)) = 91 := by
  decide
