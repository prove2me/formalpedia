-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_972
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:48:52.682692+00:00
-- url     : https://prove2.me/submissions/0b1138bc-9f2f-4487-8a23-48a0eec11a22

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

lemma degreeUnionBranch62_972_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 35 6 degreeUnionState62_972 [6,10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_972_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_972_oai
