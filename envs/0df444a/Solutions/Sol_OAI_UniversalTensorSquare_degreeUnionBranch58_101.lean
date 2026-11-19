-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_101
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:41:15.169598+00:00
-- url     : https://prove2.me/submissions/d94e2298-6324-4b63-91f5-de009a56d945

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_101_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 42 4 degreeUnionState58_101 [4,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_101_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_101_oai
