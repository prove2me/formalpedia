-- Prove2me | solution 1 for actuarial_f_anti_franking_illustrative_floor_above_minimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:03:16.009223+00:00
-- url     : https://prove2.me/submissions/0ca9ef48-ef2e-4e19-b76b-ba034f582e5b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpIllustrativeProtectedFloor

open ActuarialUnderpinsF



theorem solution
    (gmpMinimum protectedExcess current : ℝ) :
    gmpMinimum + protectedExcess ≤
      gmpIllustrativeProtectedFloor gmpMinimum protectedExcess current := by
  exact le_max_right _ _
