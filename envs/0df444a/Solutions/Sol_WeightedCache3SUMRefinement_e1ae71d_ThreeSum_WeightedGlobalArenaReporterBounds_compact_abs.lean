-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds.compact_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:51:57.785741+00:00
-- url     : https://prove2.me/submissions/e44eb2c5-cbc8-4bd2-8ab4-80e3b252bf3c

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaReporterBounds
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_index_lt


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
open Light WeightedGlobalArenaLayout LightOriginalSurvivors
open WeightedGlobalNativeMomentBounds WeightedGlobalMomentWeightBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
theorem _root_.solution (keys : ℕ→ℕ) (values : ℕ→ℤ) (n U : ℕ)
    (h : ∀ i<n, |values i|≤(U : ℤ)) :
    ∀ j<(indices keys n).length, |LightWeightedGlobalPostSelection.compact keys values n j|≤(U : ℤ) := by
  intro j hj
  exact h _ (index_lt hj)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaReporterBounds
