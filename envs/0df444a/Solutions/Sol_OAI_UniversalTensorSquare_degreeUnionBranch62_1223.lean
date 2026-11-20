-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1223
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:42:36.996153+00:00
-- url     : https://prove2.me/submissions/420564df-46e5-4315-bb4c-a3b142690217

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

lemma degreeUnionBranch62_1223_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 26 11 degreeUnionState62_1223 [11,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1223_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1223_oai
