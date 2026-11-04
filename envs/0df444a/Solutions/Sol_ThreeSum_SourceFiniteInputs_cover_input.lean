-- Prove2me | solution 1 for ThreeSum.SourceFiniteInputs.cover_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:30.486882+00:00
-- url     : https://prove2.me/submissions/047d5c43-00d7-4f6f-897d-8343f11cec93

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Theorems.Thm_ThreeSum_BlockSourceCoverInput_of_cover


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule
namespace ThreeSum.SourceFiniteInputs
theorem _root_.solution {μ : ℕ → ℤ} {free h J : ℕ} (H : LightCoverKeyData.Stored μ free h J) :
    BlockSourceCoverInput.Input μ h (maps free h) (candidates free h) (leftCounts free h) (rightCounts free h) :=
  BlockSourceCoverInput.of_cover H.data H.rows H.indices
end ThreeSum.SourceFiniteInputs
