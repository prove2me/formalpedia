-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_246
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:14:37.845896+00:00
-- url     : https://prove2.me/submissions/6940a17b-ade2-4f88-88ca-2f8220eb3f3a

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

lemma degreeUnionBranch62_246_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 24 6 degreeUnionState62_246 [6,8,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_246_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_246_oai
