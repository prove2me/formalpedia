-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivors.index_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:33.76367+00:00
-- url     : https://prove2.me/submissions/fc22070b-ff45-40cd-8329-2da555118a72

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_mem

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable
namespace ThreeSum.LightOriginalSurvivors
theorem _root_.solution {keys : ℕ → ℕ} {n j : ℕ} (hj : j < (indices keys n).length) :
    index keys n j < n := List.mem_range.mp (List.mem_filter.mp (index_mem hj)).1
end ThreeSum.LightOriginalSurvivors
