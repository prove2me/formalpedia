-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_172
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:39:36.105695+00:00
-- url     : https://prove2.me/submissions/e7b0fb85-0410-4d7f-9ae0-a44e8cc1b7f3

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

lemma degreeUnionBranch62_172_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 9 degreeUnionState62_172 [9,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_172_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_172_oai
