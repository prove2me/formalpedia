-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.local_envelope_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:59:28.027458+00:00
-- url     : https://prove2.me/submissions/8e7099c5-02a7-44f6-8142-9ce573419f32

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources

set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) :
    LocalParameterBounds.envelope (LightParameterInit.half n) ≤ localEnvelope n := by
  unfold LocalParameterBounds.envelope localEnvelope LightLocalCoverInitResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  change 2048*(half n+1)+2 ≤ 5000000*(half n+1)^2
  nlinarith only [Nat.zero_le (half n*half n)]
end ThreeSum.ThreeSumParameterResources
