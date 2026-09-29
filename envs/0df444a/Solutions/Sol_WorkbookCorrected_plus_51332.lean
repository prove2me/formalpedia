-- Prove2me | solution 1 for WorkbookCorrected.plus_51332
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:32:57.989277+00:00
-- url     : https://prove2.me/submissions/e64e042b-8938-4708-b712-0b7ae790a2f1

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : ((4:ℚ)*(1/2) ^ 4 * 1/2) + (6*(1/2) ^ 4 * 12/16) + (4*(1/2) ^ 4 * 14/16) + ((1/2) ^ 4 * 15/16) = (175:ℚ)/256 := by
  norm_num
