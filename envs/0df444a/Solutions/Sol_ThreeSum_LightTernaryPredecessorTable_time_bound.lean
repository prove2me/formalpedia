-- Prove2me | solution 1 for ThreeSum.LightTernaryPredecessorTable.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:26.205722+00:00
-- url     : https://prove2.me/submissions/b64805f3-4f81-4a67-8290-b60bd821977e

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryPredecessorTable
theorem _root_.solution (N L n : ℕ) : time N L n≤4000*(N+L+1)^2*(n+1) := by
  have hp := LightTernaryPredecessor.time_bound N L
  have hd := LightTernaryCodes.digit_time_bound (2*N)
  have hsqr : N+L+1≤(N+L+1)^2 := le_self_pow (by omega) (by decide)
  have hsmall : 400*(2*N+1)+200≤1000*(N+L+1)^2 := by omega
  have hr : LightTernaryPredecessor.time N L+LightTernaryCodes.digitTime (2*N)+200≤
      4000*(N+L+1)^2 := by
    calc
      _ ≤ 3000*(N+L+1)^2+(400*(2*N+1)+200) := by omega
      _ ≤ 3000*(N+L+1)^2+1000*(N+L+1)^2 := Nat.add_le_add_left hsmall _
      _ = _ := by ring
  have hK : 1≤(N+L+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_left n hr
  unfold time
  nlinarith [hm,hK]
end ThreeSum.LightTernaryPredecessorTable
