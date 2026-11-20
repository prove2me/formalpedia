-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_882
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:08:33.727459+00:00
-- url     : https://prove2.me/submissions/c990adc9-3e25-4f46-bb64-57792f80a5d2

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

lemma degreeUnionBranch62_882_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 27 4 degreeUnionState62_882 [4,7,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_882_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_882_oai
