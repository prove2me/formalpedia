-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1249
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:50:31.718057+00:00
-- url     : https://prove2.me/submissions/44e2882d-c0b4-44f2-b5e1-8a35d2d2227a

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

lemma degreeUnionBranch62_1249_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 28 4 degreeUnionState62_1249 [4,8,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1249_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1249_oai
