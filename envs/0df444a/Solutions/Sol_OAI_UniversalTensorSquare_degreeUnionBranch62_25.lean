-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:18:27.697203+00:00
-- url     : https://prove2.me/submissions/f93c7bba-370d-4266-af3c-4141334a6cf0

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

lemma degreeUnionBranch62_25_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 39 11 degreeUnionState62_25 [11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_25_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_25_oai
