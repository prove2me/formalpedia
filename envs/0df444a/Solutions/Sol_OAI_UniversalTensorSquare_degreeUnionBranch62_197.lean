-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_197
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:49:58.707192+00:00
-- url     : https://prove2.me/submissions/6e973fa7-6e8c-4b63-810e-6f443be59d87

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

lemma degreeUnionBranch62_197_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 5 degreeUnionState62_197 [5,10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_197_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_197_oai
