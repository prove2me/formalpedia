-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1015
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:01:00.625497+00:00
-- url     : https://prove2.me/submissions/bae82e53-c4b5-43bd-899c-ffcda38b96f2

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

lemma degreeUnionBranch62_1015_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 5 degreeUnionState62_1015 [5,8,8,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1015_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1015_oai
