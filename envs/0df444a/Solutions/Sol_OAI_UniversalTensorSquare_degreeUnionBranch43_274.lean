-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_274
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:40:13.383389+00:00
-- url     : https://prove2.me/submissions/ca049cc5-3ddc-408c-969d-c9ad118af7ea

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

lemma degreeUnionBranch43_274_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 15 12 degreeUnionState43_274 [12,16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_274_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_274_oai
