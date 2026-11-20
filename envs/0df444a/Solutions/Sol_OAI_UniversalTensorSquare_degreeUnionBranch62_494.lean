-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_494
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:49:00.016543+00:00
-- url     : https://prove2.me/submissions/16578688-b671-40e8-8c52-77760f0bd4dc

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

lemma degreeUnionBranch62_494_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 10 degreeUnionState62_494 [10,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_494_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_494_oai
