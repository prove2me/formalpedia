-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_88
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:51:19.163186+00:00
-- url     : https://prove2.me/submissions/e1993b0a-da1c-47aa-ac85-f859fd445646

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

lemma degreeUnionBranch58_88_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 34 11 degreeUnionState58_88 [11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_88_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_88_oai
