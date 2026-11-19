-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1066
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:22:57.838201+00:00
-- url     : https://prove2.me/submissions/5021a9c3-293f-412c-aa54-777bac3be542

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

lemma degreeUnionBranch62_1066_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 21 9 degreeUnionState62_1066 [9,10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1066_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1066_oai
