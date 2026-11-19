-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_731
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:41:45.220191+00:00
-- url     : https://prove2.me/submissions/e624aa1f-9f55-40db-81a7-11be49f355be

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

lemma degreeUnionBranch43_731_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 1 42 degreeUnionState43_731 [42] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_731_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_731_oai
