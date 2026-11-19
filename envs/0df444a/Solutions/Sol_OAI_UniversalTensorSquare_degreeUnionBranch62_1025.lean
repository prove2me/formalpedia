-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1025
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:09:50.597096+00:00
-- url     : https://prove2.me/submissions/65b6dcf3-377b-419a-bb16-92c0c47c7bc5

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

lemma degreeUnionBranch62_1025_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 3 degreeUnionState62_1025 [3,8,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1025_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1025_oai
