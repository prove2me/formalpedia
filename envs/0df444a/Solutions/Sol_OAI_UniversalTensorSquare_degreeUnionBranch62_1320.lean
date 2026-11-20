-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1320
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:21:21.25439+00:00
-- url     : https://prove2.me/submissions/69d3e8f2-53b9-47f4-8ec8-a8f19cecf11b

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_1320_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 24 12 degreeUnionState62_1320 [12,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1320_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1320_oai
