-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1172
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:21:40.175216+00:00
-- url     : https://prove2.me/submissions/10def1b3-8b3e-4a65-8064-3fe5d8940dbc

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

lemma degreeUnionBranch62_1172_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 4 degreeUnionState62_1172 [4,9,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1172_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1172_oai
