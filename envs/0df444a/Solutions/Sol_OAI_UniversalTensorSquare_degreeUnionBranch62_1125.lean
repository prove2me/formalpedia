-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1125
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:52:58.243503+00:00
-- url     : https://prove2.me/submissions/348ae510-eee5-4641-8f63-13b96334b1ae

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

lemma degreeUnionBranch62_1125_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 42 7 degreeUnionState62_1125 [7,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1125_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1125_oai
