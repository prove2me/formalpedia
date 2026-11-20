-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1250
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:50:44.002708+00:00
-- url     : https://prove2.me/submissions/a7a72389-e939-4c66-98ae-65d6e68e44a6

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

lemma degreeUnionBranch62_1250_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 5 degreeUnionState62_1250 [5,8,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1250_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1250_oai
