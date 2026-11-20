-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_304
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:49:17.260176+00:00
-- url     : https://prove2.me/submissions/e2ca1159-daa4-4c3c-889a-3dfe8784a6b4

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

lemma degreeUnionBranch62_304_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 8 degreeUnionState62_304 [8,9,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_304_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_304_oai
