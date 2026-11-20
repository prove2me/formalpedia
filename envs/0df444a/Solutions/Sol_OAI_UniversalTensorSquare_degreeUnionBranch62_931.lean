-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_931
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:43:12.281874+00:00
-- url     : https://prove2.me/submissions/0899bf0c-9e62-4988-9b0e-2f885d55fc52

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

lemma degreeUnionBranch62_931_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 12 degreeUnionState62_931 [12,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_931_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_931_oai
