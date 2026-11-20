-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1180
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:21:57.596562+00:00
-- url     : https://prove2.me/submissions/3b2db623-e019-485a-bac8-5ffd7b8a8108

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

lemma degreeUnionBranch62_1180_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 4 degreeUnionState62_1180 [4,10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1180_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1180_oai
