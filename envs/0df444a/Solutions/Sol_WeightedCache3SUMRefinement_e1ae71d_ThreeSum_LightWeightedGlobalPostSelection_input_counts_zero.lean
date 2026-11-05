-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPostSelection.input_counts_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:54:02.036638+00:00
-- url     : https://prove2.me/submissions/05b84565-4bb4-4fdf-84b6-d4a29e3921ba

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelectionClosed

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPostSelection
open Light TernaryMomentSchedule
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPostSelection
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : LightOriginalSurvivorPair.Layout) (scratch matrix : ℕ) :
    (args S c scratch matrix).getD 34 0 = 0 ∧
    (args S c scratch matrix).getD 36 0 = 0 ∧
    (args S c scratch matrix).getD 53 0 = 0 ∧
    (args S c scratch matrix).getD 76 0 = 0 := by
  exact ⟨rfl,rfl,rfl,rfl⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPostSelection
