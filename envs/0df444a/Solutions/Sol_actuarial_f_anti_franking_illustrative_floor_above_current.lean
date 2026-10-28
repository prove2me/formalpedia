-- Prove2me | solution 1 for actuarial_f_anti_franking_illustrative_floor_above_current
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:02:02.311+00:00
-- url     : https://prove2.me/submissions/b61fadfa-326f-40b8-98dc-a8c622a0435e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpIllustrativeProtectedFloor

open ActuarialUnderpinsF



theorem solution
    (gmpMinimum protectedExcess current : ℝ) :
    current ≤ gmpIllustrativeProtectedFloor
      gmpMinimum protectedExcess current := by
  exact le_max_left _ _
