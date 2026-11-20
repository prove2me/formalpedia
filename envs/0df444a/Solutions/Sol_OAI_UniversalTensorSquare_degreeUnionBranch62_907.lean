-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_907
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:24:46.328639+00:00
-- url     : https://prove2.me/submissions/a7ef0e8c-a4ac-45c6-9e18-c26a1ecdb453

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

lemma degreeUnionBranch62_907_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 3 degreeUnionState62_907 [3,7,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_907_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_907_oai
