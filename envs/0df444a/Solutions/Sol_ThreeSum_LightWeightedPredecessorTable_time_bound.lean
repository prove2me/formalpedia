-- Prove2me | solution 1 for ThreeSum.LightWeightedPredecessorTable.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:22.982834+00:00
-- url     : https://prove2.me/submissions/ed6365b9-a105-41bc-9a8f-52d21d94cb14

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution (N L n : ℕ) : time N L n≤4000*(N+L+1)^2*(n+1) := by
  have hp := LightWeightedPredecessor.time_bound N L
  have hd := LightTernaryCodes.digit_time_bound (2*N)
  have hsqr : N+L+1≤(N+L+1)^2 := le_self_pow (by omega) (by decide)
  have hsmall : 400*(2*N+1)+200≤1000*(N+L+1)^2 := by omega
  have hr : LightWeightedPredecessor.time N L+LightTernaryCodes.digitTime (2*N)+200≤
      4000*(N+L+1)^2 := by
    calc
      _ ≤ 3000*(N+L+1)^2+(400*(2*N+1)+200) := by omega
      _ ≤ 3000*(N+L+1)^2+1000*(N+L+1)^2 := Nat.add_le_add_left hsmall _
      _ = _ := by ring
  have hK : 1≤(N+L+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left n hr
  unfold time
  nlinarith [hm,hK]
end ThreeSum.LightWeightedPredecessorTable
