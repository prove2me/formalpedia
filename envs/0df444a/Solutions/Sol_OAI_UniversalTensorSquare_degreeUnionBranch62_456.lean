-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_456
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:36.092171+00:00
-- url     : https://prove2.me/submissions/44604d8a-3de6-4f16-b80c-75f4091912e2

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

lemma degreeUnionBranch62_456_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 8 degreeUnionState62_456 [8,8,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_456_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_456_oai
