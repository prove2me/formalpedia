-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_395
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:57:55.772052+00:00
-- url     : https://prove2.me/submissions/b1306329-5fa8-469e-8d4b-46e6adf442be

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

lemma degreeUnionBranch43_395_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 26 6 degreeUnionState43_395 [6,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_395_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_395_oai
