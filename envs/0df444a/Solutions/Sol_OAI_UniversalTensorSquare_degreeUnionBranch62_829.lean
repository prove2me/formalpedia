-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_829
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:40:03.667013+00:00
-- url     : https://prove2.me/submissions/bd3aea3d-6d7c-4174-9024-91e845b51493

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

lemma degreeUnionBranch62_829_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 9 degreeUnionState62_829 [9,13,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_829_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_829_oai
