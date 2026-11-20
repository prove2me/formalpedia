-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_355
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:26:35.002057+00:00
-- url     : https://prove2.me/submissions/8a674b74-45c0-40de-ac8f-fcdf4ccd483f

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

lemma degreeUnionBranch62_355_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 22 7 degreeUnionState62_355 [7,9,11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_355_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_355_oai
