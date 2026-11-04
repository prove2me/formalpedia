-- Prove2me | solution 1 for ThreeSum.LightTernaryFixedChannelLoop.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:13.821018+00:00
-- url     : https://prove2.me/submissions/f9e2920c-ab1e-42f5-b102-832665985226

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_time_le_length
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_length_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryFixedChannelLoop
theorem _root_.solution (terms arity C : ℕ) (cost : Channel→ℕ)
    (hcost : ∀ c∈TernaryMomentSchedule.channels terms, cost c≤C) :
    time (TernaryMomentSchedule.channels terms) cost arity≤terms^2*(arity+2+C) := by
  exact (time_le_length _ arity C cost hcost).trans
    (Nat.mul_le_mul_right _ (TernaryMomentSchedule.length_le terms))
end ThreeSum.LightTernaryFixedChannelLoop
