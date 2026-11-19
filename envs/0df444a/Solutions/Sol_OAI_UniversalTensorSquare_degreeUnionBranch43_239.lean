-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_239
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:34:36.956658+00:00
-- url     : https://prove2.me/submissions/20e4f5cf-a093-4753-8c32-6dddc6539b44

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

lemma degreeUnionBranch43_239_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 17 13 degreeUnionState43_239 [13,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_239_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_239_oai
