-- Prove2me | solution 1 for ThreeSum.LightSourceBuild.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:29.661088+00:00
-- url     : https://prove2.me/submissions/ebf8b0c3-4428-425c-b2e8-98ce3ca3189d

import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBuild
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBuild
theorem _root_.solution (N n p m U D E : ℕ) :
    time N n p m U D E ≤
      278*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      157*n*(Nat.log 2 (E+1)+1)+13*m+169 := by
  have hh := LightSourceHistogram.time_bound N p m U D
  have hg := LightSourceGather.time_bound n E
  unfold time
  omega
end ThreeSum.LightSourceBuild
