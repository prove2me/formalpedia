-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_34
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:17:27.411763+00:00
-- url     : https://prove2.me/submissions/ddf1e86a-8dca-4303-b693-8f50a66c6d5b

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

lemma degreeUnionBranch62_34_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 38 11 degreeUnionState62_34 [11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_34_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_34_oai
