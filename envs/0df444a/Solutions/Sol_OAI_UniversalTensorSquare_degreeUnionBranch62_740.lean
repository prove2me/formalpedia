-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_740
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:01:11.031479+00:00
-- url     : https://prove2.me/submissions/2cb0f31a-7ccb-47da-ab03-6b2c86193b3b

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

lemma degreeUnionBranch62_740_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 6 degreeUnionState62_740 [6,9,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_740_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_740_oai
