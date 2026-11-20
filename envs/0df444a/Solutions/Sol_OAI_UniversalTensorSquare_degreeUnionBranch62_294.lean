-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_294
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:40:08.841296+00:00
-- url     : https://prove2.me/submissions/4a252bb2-8a25-409e-9f2c-3cd4dc29a2cd

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

lemma degreeUnionBranch62_294_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 4 degreeUnionState62_294 [4,8,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_294_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_294_oai
