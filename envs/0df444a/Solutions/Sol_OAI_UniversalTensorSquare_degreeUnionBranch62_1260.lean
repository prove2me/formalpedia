-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1260
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:54:47.164198+00:00
-- url     : https://prove2.me/submissions/b52ae165-de95-4568-bb68-3132837eeec6

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

lemma degreeUnionBranch62_1260_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 3 degreeUnionState62_1260 [3,8,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1260_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1260_oai
