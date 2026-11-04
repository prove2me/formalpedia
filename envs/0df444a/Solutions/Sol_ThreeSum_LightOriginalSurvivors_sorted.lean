-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivors.sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:46.18382+00:00
-- url     : https://prove2.me/submissions/1e6f5055-9183-4237-a439-65c181599eac

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivors
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_strict

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivors
open LightOriginalBucketFilter LightOriginalCollisionCleanup
attribute [local instance] Classical.propDecidable
namespace ThreeSum.LightOriginalSurvivors
theorem _root_.solution {keys : ℕ → ℕ} {n : ℕ} (values : ℕ → ℤ)
    (hs : ∀ i j, i < j → j < n → values i < values j) :
    ∀ i j, i < j → j < (indices keys n).length →
      values (index keys n i) < values (index keys n j) := by
  intro i j hij hj
  exact hs _ _ (index_strict hij hj) (index_lt hj)
end ThreeSum.LightOriginalSurvivors
