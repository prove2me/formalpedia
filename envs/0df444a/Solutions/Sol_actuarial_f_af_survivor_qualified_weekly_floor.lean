-- Prove2me | solution 1 for actuarial_f_af_survivor_qualified_weekly_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:02:56.423982+00:00
-- url     : https://prove2.me/submissions/7cca1cc1-ccea-4393-9c10-bf97a7cf6458

import Mathlib
import Definitions.Def_actuarial_f_afRelevantAggregateWeekly
import Definitions.Def_actuarial_f_afSurvivorSection87WeeklyFloor
open ActuarialUnderpinsF

theorem solution
    (cessation death gpd t : ℕ)
    (relevant current memberBase appropriate later excludedTransferGrowth : ℝ)
    (hcess : cessation < min death gpd) (hpay : death < t)
    (hrel : memberBase / 2 < relevant)
    (hgmp : memberBase / 2 + excludedTransferGrowth < current) :
    afSurvivorSection87WeeklyFloor cessation death gpd t
      false false true false true relevant current memberBase
      appropriate later excludedTransferGrowth =
    afRelevantAggregateWeekly relevant (current - memberBase / 2 - excludedTransferGrowth)
      appropriate later := by
  unfold afSurvivorSection87WeeklyFloor
  rw [if_pos ⟨hcess, hpay, rfl, rfl, rfl, rfl, hrel, hgmp⟩]
  simp
