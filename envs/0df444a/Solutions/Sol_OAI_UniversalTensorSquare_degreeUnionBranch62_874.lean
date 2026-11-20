-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_874
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:07:59.754743+00:00
-- url     : https://prove2.me/submissions/0f7d2428-1595-4923-9576-309906805fb1

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

lemma degreeUnionBranch62_874_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 7 degreeUnionState62_874 [7,9,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_874_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_874_oai
