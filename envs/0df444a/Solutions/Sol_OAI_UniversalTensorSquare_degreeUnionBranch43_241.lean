-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_241
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:34:55.994185+00:00
-- url     : https://prove2.me/submissions/4a755e71-34fa-4799-a564-e2a5cacb8e6b

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

lemma degreeUnionBranch43_241_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 4 degreeUnionState43_241 [4,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_241_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_241_oai
