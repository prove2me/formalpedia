-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_992
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:54:59.693188+00:00
-- url     : https://prove2.me/submissions/e7971508-f98d-46e8-8c5f-6794e8213fcd

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

lemma degreeUnionBranch62_992_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 20 10 degreeUnionState62_992 [10,10,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_992_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_992_oai
