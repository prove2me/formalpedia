-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_431
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:05:15.686338+00:00
-- url     : https://prove2.me/submissions/4f179fbc-3887-4838-b212-14137d8c6b76

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

lemma degreeUnionBranch62_431_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 5 degreeUnionState62_431 [5,8,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_431_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_431_oai
