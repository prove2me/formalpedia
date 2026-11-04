-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivors.keys_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:14.795358+00:00
-- url     : https://prove2.me/submissions/4fcc3208-22cc-4399-af2a-5ffba4e24dde

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_mem
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_strict
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_surviving_keys_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable
namespace ThreeSum.LightOriginalSurvivors
theorem _root_.solution {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i < (indices keys n).length) (hj : j < (indices keys n).length)
    (he : keys (index keys n i) = keys (index keys n j)) : i = j := by
  have hh := surviving_keys_injective (index_mem hi) (index_mem hj) he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (Nat.ne_of_lt (index_strict h hj)) hh
  · exact (Nat.ne_of_lt (index_strict h hi)) hh.symm
end ThreeSum.LightOriginalSurvivors
