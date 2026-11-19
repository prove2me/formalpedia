-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:35:50.612548+00:00
-- url     : https://prove2.me/submissions/6fd54976-1b80-4494-a8c0-e2c605310231

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

lemma degreeUnionBranch43_25_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 26 7 degreeUnionState43_25 [7,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_25_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_25_oai
