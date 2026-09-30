-- Prove2me | solution 1 for WorkbookCorrected.plus_73622
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T19:38:42.914828+00:00
-- url     : https://prove2.me/submissions/ac6aa148-04ab-414f-9207-50ccd200ebbb

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 16 4) = (Nat.choose (12+4) 4) := by
  decide
