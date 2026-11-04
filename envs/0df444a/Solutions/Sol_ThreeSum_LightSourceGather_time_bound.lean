-- Prove2me | solution 1 for ThreeSum.LightSourceGather.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:11.409532+00:00
-- url     : https://prove2.me/submissions/61acabe8-8c37-4e39-8945-e6d6fb22618f

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Definitions.Def_Submission_ThreeSum_LightSourceGather

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceGather
theorem _root_.solution (n U : ℕ) : time n U ≤ 157*n*(Nat.log 2 (U+1)+1)+6 := by
  unfold time LightResidues.residueBudget
  nlinarith
end ThreeSum.LightSourceGather
