-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_488
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:38:59.660496+00:00
-- url     : https://prove2.me/submissions/77c680fb-d8bb-4bef-a0b6-db5b4d033d75

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

lemma degreeUnionBranch62_488_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 4 degreeUnionState62_488 [4,7,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_488_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_488_oai
