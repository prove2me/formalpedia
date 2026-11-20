-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_317
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:58:22.487302+00:00
-- url     : https://prove2.me/submissions/36157077-b988-4158-95de-6a226c06b1d0

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

lemma degreeUnionBranch62_317_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 5 degreeUnionState62_317 [5,8,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_317_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_317_oai
