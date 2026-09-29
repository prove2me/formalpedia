-- Prove2me | solution 1 for WorkbookCorrected.plus_35143
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:45:24.181987+00:00
-- url     : https://prove2.me/submissions/1286ea70-b90d-41fe-afb1-4d1746b3d155

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 12)/(((Nat.factorial 3)*(Nat.factorial 9))) = 220 := by
  decide
