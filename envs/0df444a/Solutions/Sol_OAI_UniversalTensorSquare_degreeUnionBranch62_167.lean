-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_167
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:39:05.009201+00:00
-- url     : https://prove2.me/submissions/2e82298e-9a12-4665-a9cc-6703febebf12

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

lemma degreeUnionBranch62_167_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 28 4 degreeUnionState62_167 [4,9,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_167_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_167_oai
