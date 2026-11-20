-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_982
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:54:45.487517+00:00
-- url     : https://prove2.me/submissions/e5f543d4-fdda-4d26-ab59-299054628a80

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

lemma degreeUnionBranch62_982_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 8 degreeUnionState62_982 [8,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_982_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_982_oai
