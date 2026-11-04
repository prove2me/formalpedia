-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaReporterBounds.compact_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:14:23.446347+00:00
-- url     : https://prove2.me/submissions/4afedde2-1d5e-45ac-a8f7-ecf282a803ef

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds
namespace ThreeSum.WeightedGlobalArenaReporterBounds
theorem _root_.solution (keys : ℕ→ℕ) (values : ℕ→ℤ) (n U : ℕ)
    (h : ∀ i<n, |values i|≤(U : ℤ)) :
    ∀ j<(indices keys n).length, |LightWeightedGlobalPostSelection.compact keys values n j|≤(U : ℤ) := by
  intro j hj
  exact h _ (index_lt hj)
end ThreeSum.WeightedGlobalArenaReporterBounds
