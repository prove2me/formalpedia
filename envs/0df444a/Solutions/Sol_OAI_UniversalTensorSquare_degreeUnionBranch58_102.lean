-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_102
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:41:21.506238+00:00
-- url     : https://prove2.me/submissions/fd6efaad-5ada-4853-bd24-c560720ef3f0

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_102_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 41 5 degreeUnionState58_102 [5,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_102_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_102_oai
