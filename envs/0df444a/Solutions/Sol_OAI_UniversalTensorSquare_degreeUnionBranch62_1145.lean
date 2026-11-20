-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1145
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:07:46.311822+00:00
-- url     : https://prove2.me/submissions/e79cd4d9-c617-4526-8861-f541c1d5ed89

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

lemma degreeUnionBranch62_1145_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 4 degreeUnionState62_1145 [4,8,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1145_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1145_oai
