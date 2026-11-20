-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_395
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:42:37.912623+00:00
-- url     : https://prove2.me/submissions/b155cec1-987c-4771-9bb4-391b99456236

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

lemma degreeUnionBranch62_395_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 43 5 degreeUnionState62_395 [5,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_395_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_395_oai
