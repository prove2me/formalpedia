-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.program_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:08.14719+00:00
-- url     : https://prove2.me/submissions/3d534c6c-4660-40e1-92ea-683f7aa949e1

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
theorem _root_.solution : program[3]? = some (LightTernaryCodes.digitBody 5) := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
