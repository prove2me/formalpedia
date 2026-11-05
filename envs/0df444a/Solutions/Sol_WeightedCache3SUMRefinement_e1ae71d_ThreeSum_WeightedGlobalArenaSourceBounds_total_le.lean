-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds.total_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:09:13.774227+00:00
-- url     : https://prove2.me/submissions/48e75bc2-ba92-4242-8b31-3b6da35bd0f3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceBounds
import Theorems.Thm_ThreeSum_LightHistogram_count_le

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
theorem _root_.solution (M NL NR : ℕ) (left right : ℕ→ℤ) :
    WantedResidueKeys.total M left right NL NR 0≤NL*NR := by
  unfold WantedResidueKeys.total WantedPairs.count
  calc
    _≤∑ _i∈Finset.range NL, NR := by
      apply Finset.sum_le_sum
      intro i hi
      exact LightHistogram.count_le _ _ _
    _=NL*NR := by simp
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceBounds
