-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_919
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:31:25.105795+00:00
-- url     : https://prove2.me/submissions/eed2bf75-d496-40a0-b17a-624d35183f4d

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

lemma degreeUnionBranch62_919_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 9 degreeUnionState62_919 [9,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_919_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_919_oai
