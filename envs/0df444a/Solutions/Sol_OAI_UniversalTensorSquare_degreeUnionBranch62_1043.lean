-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1043
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:14:40.353594+00:00
-- url     : https://prove2.me/submissions/fdf2179c-3d50-4fb5-bed4-123da725d2a0

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

lemma degreeUnionBranch62_1043_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 7 degreeUnionState62_1043 [7,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1043_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1043_oai
