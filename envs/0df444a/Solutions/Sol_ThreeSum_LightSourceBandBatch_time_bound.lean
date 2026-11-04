-- Prove2me | solution 1 for ThreeSum.LightSourceBandBatch.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:10.337774+00:00
-- url     : https://prove2.me/submissions/67fb5ba1-fc3c-4da4-83e1-9e8425a2b643

import Definitions.Def_Submission_ThreeSum_LightSourceBandStep
import Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
import Theorems.Thm_ThreeSum_SourceBandLayout_capacity_product_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandBatch
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBandBatch
theorem _root_.solution (n g p m U D : ℕ) (hg : 0 < g) :
    time n g p m U D ≤
      996*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+size n g*(233*m+1713)+20 := by
  have hc := capacity_product_le n g hg
  have hh := Nat.mul_le_mul_left 498 (Nat.mul_le_mul_right
    (Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1) hc)
  unfold time LightSourceBandStep.time LightSourceBandStep.charge
  nlinarith
end ThreeSum.LightSourceBandBatch
