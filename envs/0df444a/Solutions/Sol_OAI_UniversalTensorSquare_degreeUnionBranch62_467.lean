-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_467
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:57.55708+00:00
-- url     : https://prove2.me/submissions/c229f05a-b738-4d21-9cd1-6911d17add25

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

lemma degreeUnionBranch62_467_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 5 degreeUnionState62_467 [5,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_467_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_467_oai
