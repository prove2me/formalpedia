-- Prove2me | solution 1 for ThreeSum.LightOriginalBucketFilter.lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:59.177705+00:00
-- url     : https://prove2.me/submissions/b9907a6a-12b8-4a22-980a-27e65709fcc6

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
theorem _root_.solution (keys counts : ℕ → ℕ) (n : ℕ) :
    (good keys counts n).length≤n ∧ (bad keys counts n).length≤n := by
  constructor <;> apply (List.length_filter_le _ _).trans_eq (List.length_range : (List.range n).length=n)
end ThreeSum.LightOriginalBucketFilter
