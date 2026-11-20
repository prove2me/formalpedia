-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_126
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:54:41.007177+00:00
-- url     : https://prove2.me/submissions/4912205f-3510-4011-8575-61dbd965ce95

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

lemma degreeUnionBranch62_126_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 7 degreeUnionState62_126 [7,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_126_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_126_oai
