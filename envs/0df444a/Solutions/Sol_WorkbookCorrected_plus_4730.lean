-- Prove2me | solution 1 for WorkbookCorrected.plus_4730
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:56:59.017889+00:00
-- url     : https://prove2.me/submissions/18bc8ab8-c7e7-464d-875e-f1492ba7e92f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : 2005 * 2004 * 2003 / (Nat.factorial 3) = 2 * 5 * 167 * 401 * 2003 := by
  decide
