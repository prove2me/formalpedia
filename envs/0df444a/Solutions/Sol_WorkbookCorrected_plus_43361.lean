-- Prove2me | solution 1 for WorkbookCorrected.plus_43361
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:28:11.196893+00:00
-- url     : https://prove2.me/submissions/7b06c509-4a99-4451-8cdd-d6d9bdc4c775

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : ((1:ℚ)/3 + 2/3 * (1/2 * (1 - 1/56))) = (37:ℚ)/56 := by
  norm_num
