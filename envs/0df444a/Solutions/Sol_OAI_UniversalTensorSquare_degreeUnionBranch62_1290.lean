-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1290
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:07:46.189275+00:00
-- url     : https://prove2.me/submissions/94ce0480-a3e8-4c46-a5de-4b9c2a8353a1

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

lemma degreeUnionBranch62_1290_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 6 degreeUnionState62_1290 [6,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1290_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1290_oai
