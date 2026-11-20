-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_295
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:40:15.105512+00:00
-- url     : https://prove2.me/submissions/469fa571-97e8-467f-81ea-d70bb0dc4f4e

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

lemma degreeUnionBranch62_295_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 5 degreeUnionState62_295 [5,8,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_295_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_295_oai
