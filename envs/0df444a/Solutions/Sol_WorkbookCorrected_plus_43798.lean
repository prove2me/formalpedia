-- Prove2me | solution 1 for WorkbookCorrected.plus_43798
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:27:43.667823+00:00
-- url     : https://prove2.me/submissions/a9b32652-1b19-4bf0-9f56-264c900cf3e7

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 52 4) = 270725 := by
  decide
