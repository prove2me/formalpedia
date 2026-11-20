-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_115
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:03:49.170178+00:00
-- url     : https://prove2.me/submissions/303fc126-eea3-4932-af9a-6b6b9700151c

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

lemma degreeUnionBranch62_115_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 4 degreeUnionState62_115 [4,10,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_115_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_115_oai
