-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_161
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:33:47.570474+00:00
-- url     : https://prove2.me/submissions/dcc163e2-e858-4e36-9333-b9f16ecb94e4

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

lemma degreeUnionBranch62_161_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 29 4 degreeUnionState62_161 [4,8,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_161_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_161_oai
