-- Prove2me | solution 1 for actuarial_f_lpi_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:15.316019+00:00
-- url     : https://prove2.me/submissions/5be60287-be19-44fd-bd94-3d795106e177

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution (floor cap x : ℝ) :
    lpiRate floor cap x ≤ cap := by
  unfold lpiRate
  exact min_le_left _ _
