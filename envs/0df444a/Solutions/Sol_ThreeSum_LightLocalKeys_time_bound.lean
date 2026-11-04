-- Prove2me | solution 1 for ThreeSum.LightLocalKeys.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:27.486386+00:00
-- url     : https://prove2.me/submissions/0952b514-10c5-4ba4-96e7-b6e79e73aa44

import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalKeys
open Light
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalKeys
theorem _root_.solution (L n rows : ℕ) : time L n rows ≤ 1200*(L+1)*(n+1)*(rows+1) := by
  have hh := LightLocalKeyRow.time_bound L n
  have hper : LightLocalKeyRow.time L n+copyTime n+130 ≤ 1100*(L+1)*(n+1) := by
    unfold copyTime
    nlinarith
  have hm := Nat.mul_le_mul_left rows hper
  have he : 1200*(L+1)*(n+1)*(rows+1) = rows*(1100*(L+1)*(n+1))+20+
      (100*rows*(L+1)*(n+1)+1200*L*n+1200*L+1200*n+1180) := by ring
  unfold time
  rw [he]
  omega
end ThreeSum.LightLocalKeys
