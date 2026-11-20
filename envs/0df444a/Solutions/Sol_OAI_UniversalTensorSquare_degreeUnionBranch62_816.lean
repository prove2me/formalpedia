-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_816
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:29:29.307267+00:00
-- url     : https://prove2.me/submissions/4623974e-a9a2-41d3-b125-c18ada159f0e

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

lemma degreeUnionBranch62_816_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 23 6 degreeUnionState62_816 [6,8,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_816_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_816_oai
