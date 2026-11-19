-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_432
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:07:47.528596+00:00
-- url     : https://prove2.me/submissions/b9d72f3e-cf3b-4494-8287-81f00bb938d5

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_432_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 16 13 degreeUnionState43_432 [13,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_432_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_432_oai
