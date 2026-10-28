-- Prove2me | solution 1 for actuarial_f_af_section53_no_double_credit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:00:49.913004+00:00
-- url     : https://prove2.me/submissions/43db1f21-1528-4488-82cc-f860b47f177c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afSection53AllocationValid

open ActuarialUnderpinsF



theorem solution
    (available c109 c51 : ℝ)
    (valid : afSection53AllocationValid available c109 c51) :
    c109 + c51 ≤ max 0 available := by
  exact valid.2.2
