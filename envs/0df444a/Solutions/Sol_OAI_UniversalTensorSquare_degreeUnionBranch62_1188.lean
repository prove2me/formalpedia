-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1188
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:25:57.260736+00:00
-- url     : https://prove2.me/submissions/dc59d061-4b6e-491f-b342-0b193bb9675a

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

lemma degreeUnionBranch62_1188_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 34 4 degreeUnionState62_1188 [4,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1188_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1188_oai
