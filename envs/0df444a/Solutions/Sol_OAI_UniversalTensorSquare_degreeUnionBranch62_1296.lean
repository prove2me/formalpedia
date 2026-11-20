-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1296
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:08:17.740171+00:00
-- url     : https://prove2.me/submissions/bcccf460-2364-46d4-9da5-e6116185a8f7

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

lemma degreeUnionBranch62_1296_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 4 degreeUnionState62_1296 [4,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1296_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1296_oai
