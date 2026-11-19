-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_204
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:55.423183+00:00
-- url     : https://prove2.me/submissions/6536d678-83e5-4e3c-9e9d-a94abc952b45

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

lemma degreeUnionBranch43_204_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 28 5 degreeUnionState43_204 [5,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_204_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_204_oai
