-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.hash_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:31.822845+00:00
-- url     : https://prove2.me/submissions/4ac5468c-0334-4e67-b086-d9b49e8c5e08

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverCost
theorem _root_.solution (L n p : ℕ) :
    LightHashHistogram.time L n p p ≤ 1000*(L+1)*(n+1)*(p+1) := by
  have hm := Nat.mul_le_mul_left n (Nat.log_le_self 2 (L*p+1))
  unfold LightHashHistogram.time LightMaskHashes.time LightOneHot.time
    LightResidues.residuesTime LightResidues.residueBudget LightHistogram.histogramTime
    LightHistogram.countTime powTableTime fillTime
  ring_nf at hm ⊢
  omega
end ThreeSum.LightLocalCoverCost
