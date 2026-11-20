-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_582
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:54:47.673443+00:00
-- url     : https://prove2.me/submissions/dc6fb9ab-9d2e-4db5-9479-a4a55a2cf0e5

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

lemma degreeUnionBranch62_582_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 22 7 degreeUnionState62_582 [7,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_582_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_582_oai
