-- Prove2me | solution 1 for ThreeSum.LightSelectedPrime.pool_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:32.706286+00:00
-- url     : https://prove2.me/submissions/4269a4db-829e-4838-a5e7-f20da54cf871

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime

set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSelectedPrime
theorem _root_.solution (y : ℕ) : LightPrimePool.time y ≤ 5000*(y+1)^3 := by
  have hlog := Nat.log_le_self 2 (4*y+1)
  have hres : residueBudget (4*y)+70 ≤ 172*y+190 := by
    unfold residueBudget
    omega
  have hprim : LightPrimality.time (4*y) (4*y) ≤ 4*y*(172*y+190)+70 := by
    unfold LightPrimality.time
    exact Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.sub_le _ _) hres) _
  have hpool : LightPrimePool.time y ≤ 3*y*(4*y*(172*y+190)+170)+100 := by
    unfold LightPrimePool.time
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega
  exact hpool.trans (by nlinarith [Nat.zero_le (y^3),Nat.zero_le (y^2)])
end ThreeSum.LightSelectedPrime
