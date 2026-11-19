-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_237
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:34:23.843235+00:00
-- url     : https://prove2.me/submissions/c9aedfa1-e9fe-49da-af75-3164c33ec5b8

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

lemma degreeUnionBranch43_237_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 11 degreeUnionState43_237 [11,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_237_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_237_oai
