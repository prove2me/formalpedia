-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1298
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:11:53.762096+00:00
-- url     : https://prove2.me/submissions/2ebd7561-1c26-4b9c-a170-eab7e31c7b96

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

lemma degreeUnionBranch62_1298_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 6 degreeUnionState62_1298 [6,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1298_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1298_oai
