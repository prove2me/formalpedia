-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1161
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:13:04.013525+00:00
-- url     : https://prove2.me/submissions/38f2d873-11f7-4320-8bfe-69dbf4be0e9a

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

lemma degreeUnionBranch62_1161_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 6 degreeUnionState62_1161 [6,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1161_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1161_oai
