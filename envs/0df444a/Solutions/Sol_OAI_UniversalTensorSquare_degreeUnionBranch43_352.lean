-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_352
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:49:25.142642+00:00
-- url     : https://prove2.me/submissions/baab93b7-50bc-45b8-ac71-97a1e38aaadc

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

lemma degreeUnionBranch43_352_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 38 5 degreeUnionState43_352 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_352_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_352_oai
