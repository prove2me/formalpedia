-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_867
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:02:07.221162+00:00
-- url     : https://prove2.me/submissions/dd0886fc-f371-4a7a-be9c-f1ed1ffcef62

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

lemma degreeUnionBranch62_867_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 24 7 degreeUnionState62_867 [7,8,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_867_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_867_oai
