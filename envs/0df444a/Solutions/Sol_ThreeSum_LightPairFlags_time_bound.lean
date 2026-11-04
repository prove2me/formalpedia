-- Prove2me | solution 1 for ThreeSum.LightPairFlags.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:26.999632+00:00
-- url     : https://prove2.me/submissions/911db35c-9fb8-4141-95f4-a84fa5e614b1

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightTrimTest
import Definitions.Def_Submission_ThreeSum_LightPairFlags

set_option autoImplicit false
open ThreeSum ThreeSum.LightPairFlags
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPairFlags
theorem _root_.solution (L n : ℕ) : time L n ≤ 500*(n*n)*(L+n+1)+30 := by
  have hround : roundTime L n+12 ≤ 500*(L+n+1) := by
    unfold roundTime LightBooleanDot.time LightTrimTest.time
    omega
  have hmul := Nat.mul_le_mul_left (n*n) hround
  unfold time
  nlinarith
end ThreeSum.LightPairFlags
