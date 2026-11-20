-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_468
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:32:23.226908+00:00
-- url     : https://prove2.me/submissions/8564f913-f6cd-4cd3-a862-5767964fdae6

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

lemma degreeUnionBranch62_468_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 6 degreeUnionState62_468 [6,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_468_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_468_oai
