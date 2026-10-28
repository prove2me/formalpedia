-- Prove2me | solution 1 for actuarial_f_complete_months_six
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:09.590814+00:00
-- url     : https://prove2.me/submissions/f1a8870f-c7fe-4f94-a509-aad297867f4d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_completeMonths

open ActuarialUnderpinsF

theorem solution :
    completeMonths 0 6 = 6 := by
  unfold completeMonths; decide
