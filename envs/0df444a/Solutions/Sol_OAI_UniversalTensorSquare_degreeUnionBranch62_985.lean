-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_985
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:49:20.810959+00:00
-- url     : https://prove2.me/submissions/cd876b2d-3dff-4cb6-8f79-6bc51371e5e0

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

lemma degreeUnionBranch62_985_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 3 degreeUnionState62_985 [3,10,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_985_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_985_oai
