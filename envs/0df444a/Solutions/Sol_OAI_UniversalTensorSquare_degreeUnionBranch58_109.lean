-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_109
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:37:05.655567+00:00
-- url     : https://prove2.me/submissions/8bde69b3-b128-42a0-909c-381251428da3

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

lemma degreeUnionBranch58_109_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 34 12 degreeUnionState58_109 [12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_109_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_109_oai
