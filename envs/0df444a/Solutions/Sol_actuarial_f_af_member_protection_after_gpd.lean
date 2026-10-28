-- Prove2me | solution 1 for actuarial_f_af_member_protection_after_gpd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:04:10.667098+00:00
-- url     : https://prove2.me/submissions/05b102b5-8e98-40fe-ad34-116f37caebf0

import Mathlib
import Definitions.Def_actuarial_f_afLaterEarningsAddition
import Definitions.Def_actuarial_f_afRelevantAggregateWeekly
import Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor
open ActuarialUnderpinsF

theorem solution
    (cessation gpd t : ℕ)
    (relevant current base appropriate assumedLater excludedTransferGrowth : ℝ)
    (hcess : cessation < gpd) (hpay : gpd ≤ t)
    (hbase : base < relevant) (hgmp : base + excludedTransferGrowth < current) :
    afMemberSection87WeeklyFloor cessation gpd t
      false false true false true relevant current base appropriate
      (afLaterEarningsAddition relevant base assumedLater) excludedTransferGrowth =
    afRelevantAggregateWeekly relevant (current - base - excludedTransferGrowth)
       appropriate (afLaterEarningsAddition relevant base assumedLater) := by
  unfold afMemberSection87WeeklyFloor
  rw [if_pos ⟨hcess, hpay, rfl, rfl, rfl, rfl, hbase, hgmp⟩]
  simp [afMemberGmpExcessSinceCessation]
