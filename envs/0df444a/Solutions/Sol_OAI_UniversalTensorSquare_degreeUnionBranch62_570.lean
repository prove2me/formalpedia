-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_570
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:59:36.689074+00:00
-- url     : https://prove2.me/submissions/e5d58b7c-ec17-4ca4-97f0-1ca3d9dbfa1e

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

lemma degreeUnionBranch62_570_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 4 degreeUnionState62_570 [4,10,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_570_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_570_oai
