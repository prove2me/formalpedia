-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1093
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:32:57.400293+00:00
-- url     : https://prove2.me/submissions/9de45d00-6383-49e7-99cb-b7424f9543f3

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

lemma degreeUnionBranch62_1093_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 22 7 degreeUnionState62_1093 [7,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1093_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1093_oai
