-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_219
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:57:00.618854+00:00
-- url     : https://prove2.me/submissions/aa5400c3-bf4c-4d71-9bd8-2d66972e32b8

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

lemma degreeUnionBranch62_219_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 26 4 degreeUnionState62_219 [4,9,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_219_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_219_oai
