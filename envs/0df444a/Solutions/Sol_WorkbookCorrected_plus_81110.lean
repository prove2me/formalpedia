-- Prove2me | solution 1 for WorkbookCorrected.plus_81110
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T12:54:01.403652+00:00
-- url     : https://prove2.me/submissions/ce9185bd-310e-47b7-b4e2-fc81b916c399

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : 8 * (Nat.factorial 10) * (Nat.factorial 2) = 8 * (Nat.factorial 10) * (Nat.factorial 2) := by
  decide
