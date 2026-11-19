-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_177
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:20:07.576489+00:00
-- url     : https://prove2.me/submissions/2e2b22c4-a254-45c9-8510-5501e0b0d693

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

lemma degreeUnionBranch43_177_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 5 38 degreeUnionState43_177 [38] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_177_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_177_oai
