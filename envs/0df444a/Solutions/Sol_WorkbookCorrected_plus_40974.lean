-- Prove2me | solution 1 for WorkbookCorrected.plus_40974
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T07:13:56.680645+00:00
-- url     : https://prove2.me/submissions/805ab6d0-bcd2-400d-9fd1-8efc6f9c99ed

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem solution : (623171679694215690971693339/131362987122535807501262400:ℚ) < (32/5:ℚ) := by
  norm_num
