-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1287
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:03:08.933607+00:00
-- url     : https://prove2.me/submissions/c3fcdddc-45c7-4325-ac04-1c6656d1fd33

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

lemma degreeUnionBranch62_1287_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 3 degreeUnionState62_1287 [3,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1287_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1287_oai
