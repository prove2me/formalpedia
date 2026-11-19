-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_329
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:44:23.296299+00:00
-- url     : https://prove2.me/submissions/f0b824a4-3f9f-449d-9c34-6dee50731bea

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

lemma degreeUnionBranch43_329_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 22 21 degreeUnionState43_329 [21] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_329_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_329_oai
