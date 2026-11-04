-- Prove2me | solution 1 for ThreeSum.LightSourceHistogram.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:29.595534+00:00
-- url     : https://prove2.me/submissions/1abd3670-0904-4b72-89b8-dade2ef2be12

import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceHistogram
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceHistogram
theorem _root_.solution (n p m U D : ℕ) :
    time n p m U D ≤
      278*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+13*m+63 := by
  have hr := LightSourceResidues.time_bound n p U D
  unfold time LightHistogram.histogramTime LightHistogram.countTime fillTime
  nlinarith
end ThreeSum.LightSourceHistogram
