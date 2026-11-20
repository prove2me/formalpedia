-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_432
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:05:23.54896+00:00
-- url     : https://prove2.me/submissions/94d6d868-04fc-4e6a-87d0-c1fc6f040136

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

lemma degreeUnionBranch62_432_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 25 6 degreeUnionState62_432 [6,8,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_432_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_432_oai
