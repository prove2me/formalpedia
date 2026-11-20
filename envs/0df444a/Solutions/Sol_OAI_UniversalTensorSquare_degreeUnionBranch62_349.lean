-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_349
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:17:46.760004+00:00
-- url     : https://prove2.me/submissions/cd9d0dae-4a0b-40d4-af65-df70f0d6649b

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

lemma degreeUnionBranch62_349_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 7 degreeUnionState62_349 [7,8,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_349_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_349_oai
