-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_771
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:55:29.973845+00:00
-- url     : https://prove2.me/submissions/ac58d41e-9335-4325-957e-643843dca4d5

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

lemma degreeUnionBranch43_771_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 1 42 degreeUnionState43_771 [42] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_771_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_771_oai
