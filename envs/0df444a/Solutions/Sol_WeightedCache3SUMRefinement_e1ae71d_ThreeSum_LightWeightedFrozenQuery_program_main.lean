-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.program_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:40.832638+00:00
-- url     : https://prove2.me/submissions/2bd96bb7-507f-4f39-9938-760040fe6107

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Frozen

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open Light
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution : program[0]? = some (body 0 1 3 4 5) := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
