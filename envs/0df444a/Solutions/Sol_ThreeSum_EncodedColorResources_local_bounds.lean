-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.local_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:16.801683+00:00
-- url     : https://prove2.me/submissions/72a46822-9d7e-4428-bc29-15a1723daf3b

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Definitions.Def_WeightedCache3SUM_Alias_f93cfd5252bad152
import Theorems.Thm_ThreeSum_SourceBucketView_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : LightLocalCoverMagnitude.Bounds (half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩
end ThreeSum.EncodedColorResources
