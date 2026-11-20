-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_986
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:54:52.782043+00:00
-- url     : https://prove2.me/submissions/87b21c22-e57f-4c1b-92e2-60b9b8a40e63

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

lemma degreeUnionBranch62_986_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 4 degreeUnionState62_986 [4,10,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_986_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_986_oai
