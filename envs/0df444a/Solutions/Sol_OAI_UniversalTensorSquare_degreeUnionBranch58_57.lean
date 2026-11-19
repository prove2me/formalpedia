-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch58_57
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:46:39.48033+00:00
-- url     : https://prove2.me/submissions/c29cb58c-dc8b-4275-bd0b-94644bdac0b2

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

lemma degreeUnionBranch58_57_oai : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 34 10 degreeUnionState58_57 [10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch58_57_oai := @OAI.UniversalTensorSquare.degreeUnionBranch58_57_oai
