-- Prove2me | solution 1 for ThreeSum.LightOriginalBucketFilter.bad_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:58.10672+00:00
-- url     : https://prove2.me/submissions/0f220bde-f824-4481-ba3a-b4301256c3cb

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThreeSum.LightOriginalBucketFilter
theorem _root_.solution (keys counts : ℕ → ℕ) : bad keys counts 0=[] := rfl
end ThreeSum.LightOriginalBucketFilter
