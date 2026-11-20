-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_702
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:49:20.112281+00:00
-- url     : https://prove2.me/submissions/0c1e1cf6-78c5-4adc-bcdd-2be11b374ec3

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

lemma degreeUnionBranch62_702_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 8 degreeUnionState62_702 [8,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_702_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_702_oai
