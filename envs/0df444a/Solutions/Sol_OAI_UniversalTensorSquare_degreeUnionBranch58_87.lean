-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_87
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:51:13.133388+00:00
-- url     : https://prove2.me/submissions/c2ea9aac-503c-496b-a9ce-947e32bfb7d5

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_87_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 35 10 degreeUnionState58_87 [10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_87_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_87_oai
