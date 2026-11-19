-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_659
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:29:45.055205+00:00
-- url     : https://prove2.me/submissions/5ea4555a-d871-4908-b10f-5f49091ea288

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_659_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 25 18 degreeUnionState43_659 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_659_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_659_oai
