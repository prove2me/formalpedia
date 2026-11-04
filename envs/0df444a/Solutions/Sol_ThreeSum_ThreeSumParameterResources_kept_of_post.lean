-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.kept_of_post
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:19:10.642697+00:00
-- url     : https://prove2.me/submissions/8e79f49f-be95-45de-b0b1-c137f8baba35

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources

set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution {μ ν : ℕ→ℤ} {dst : ℕ} (H : KeptBut μ ν (work dst) dst 19) :
    Kept μ ν dst := by
  intro i hi
  exact H i ⟨by unfold work; omega,Or.inl hi⟩
end ThreeSum.ThreeSumParameterResources
