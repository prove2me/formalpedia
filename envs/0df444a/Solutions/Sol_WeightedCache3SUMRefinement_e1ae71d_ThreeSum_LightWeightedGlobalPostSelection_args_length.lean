-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPostSelection.args_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:53:07.785002+00:00
-- url     : https://prove2.me/submissions/c411ff62-156e-4598-a477-8a4e7aadeedd

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
    (args S c scratch matrix).length = 148 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPostSelection
