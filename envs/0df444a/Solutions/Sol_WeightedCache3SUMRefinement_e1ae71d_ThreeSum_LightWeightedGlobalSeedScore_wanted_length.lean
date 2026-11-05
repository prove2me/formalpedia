-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore.wanted_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:49:43.624222+00:00
-- url     : https://prove2.me/submissions/4f85ca18-8f3e-4c12-83f4-653da8040f47

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScore

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore
theorem _root_.solution (p R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :
    (LightTernaryWantedBatch.program p R S raws words maps).length=5 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScore
