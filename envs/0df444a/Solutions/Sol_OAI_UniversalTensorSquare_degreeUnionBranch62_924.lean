-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_924
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:31:45.458175+00:00
-- url     : https://prove2.me/submissions/0df16395-e0fc-4bcf-82ea-9b85cb870b63

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

lemma degreeUnionBranch62_924_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 5 degreeUnionState62_924 [5,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_924_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_924_oai
