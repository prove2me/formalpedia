-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivors.length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:00.380201+00:00
-- url     : https://prove2.me/submissions/2f8c3b58-7b3d-4840-8186-2b40292da81d

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_lengths


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable
namespace ThreeSum.LightOriginalSurvivors
theorem _root_.solution (keys : ℕ → ℕ) (n : ℕ) : (indices keys n).length ≤ n :=
  (lengths keys (counts keys n) n).1
end ThreeSum.LightOriginalSurvivors
