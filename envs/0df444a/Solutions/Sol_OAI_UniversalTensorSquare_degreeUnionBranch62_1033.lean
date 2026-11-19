-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1033
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:10:08.653097+00:00
-- url     : https://prove2.me/submissions/7a733f41-9326-4f47-a053-94e6a72b428f

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

lemma degreeUnionBranch62_1033_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 4 degreeUnionState62_1033 [4,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1033_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1033_oai
