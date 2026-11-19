-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_208
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:25:19.443562+00:00
-- url     : https://prove2.me/submissions/8bedcd5e-84b5-435c-a5dd-7d2175531765

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

lemma degreeUnionBranch43_208_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 24 9 degreeUnionState43_208 [9,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_208_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_208_oai
