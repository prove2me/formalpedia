-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_202
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:52:45.02486+00:00
-- url     : https://prove2.me/submissions/4db2da01-4d7f-496c-a9d4-8ced7afafaa5

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

lemma degreeUnionBranch62_202_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 20 10 degreeUnionState62_202 [10,10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_202_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_202_oai
