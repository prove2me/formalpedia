-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1070
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:27:29.309433+00:00
-- url     : https://prove2.me/submissions/96b84162-a572-4c1c-a62f-1fe6afd9e754

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

lemma degreeUnionBranch62_1070_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 34 5 degreeUnionState62_1070 [5,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1070_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1070_oai
