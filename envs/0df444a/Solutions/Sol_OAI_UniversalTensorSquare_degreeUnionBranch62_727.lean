-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_727
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:00:09.907179+00:00
-- url     : https://prove2.me/submissions/93e571fb-cb4d-4878-bff0-b03bc116070d

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

lemma degreeUnionBranch62_727_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 4 degreeUnionState62_727 [4,9,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_727_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_727_oai
