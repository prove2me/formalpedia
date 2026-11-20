-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_123
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:42:49.66629+00:00
-- url     : https://prove2.me/submissions/2ed2b6ee-9f82-4799-8271-4029a7883284

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

lemma degreeUnionBranch62_123_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 4 degreeUnionState62_123 [4,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_123_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_123_oai
