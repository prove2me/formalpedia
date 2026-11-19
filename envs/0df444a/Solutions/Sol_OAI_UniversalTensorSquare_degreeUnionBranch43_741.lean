-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_741
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:45:15.92999+00:00
-- url     : https://prove2.me/submissions/da7c2cd9-24ba-41c7-a2f8-dc417b53b204

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

lemma degreeUnionBranch43_741_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 31 12 degreeUnionState43_741 [12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_741_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_741_oai
