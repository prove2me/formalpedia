-- Prove2me | solution 1 for actuarial_f_af_member_topup_meets_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:04:50.232115+00:00
-- url     : https://prove2.me/submissions/4745aef8-f35f-443b-aea2-46e217e9c66e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly
import Definitions.Def_actuarial_f_afMemberSection87TopUp

open ActuarialUnderpinsF



theorem solution
    (r i t : ℕ) (scheme weekly : ℝ)
    (hdue : memberDue r i t = 1) :
    afStatutoryWeeklyToMonthly weekly ≤
      scheme + afMemberSection87TopUp r i t scheme weekly := by
  unfold afMemberSection87TopUp
  rw [hdue, mul_one]
  have := le_max_right 0 (afStatutoryWeeklyToMonthly weekly - scheme)
  linarith
