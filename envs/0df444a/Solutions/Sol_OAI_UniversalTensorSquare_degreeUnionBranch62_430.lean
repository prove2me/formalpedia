-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_430
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:00:41.963035+00:00
-- url     : https://prove2.me/submissions/8be143d0-a066-4124-acec-906c8c959fe7

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

lemma degreeUnionBranch62_430_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 4 degreeUnionState62_430 [4,8,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_430_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_430_oai
