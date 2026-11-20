-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_739
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:01:04.332847+00:00
-- url     : https://prove2.me/submissions/b8a7f982-3450-423c-a1fc-2e21d298252c

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

lemma degreeUnionBranch62_739_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 5 degreeUnionState62_739 [5,9,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_739_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_739_oai
