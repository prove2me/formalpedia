-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_264
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:31:05.933033+00:00
-- url     : https://prove2.me/submissions/afd83290-594d-48b2-9fe9-31821f2eaef0

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

lemma degreeUnionBranch62_264_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 36 6 degreeUnionState62_264 [6,7,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_264_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_264_oai
