-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_780
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:00:31.74273+00:00
-- url     : https://prove2.me/submissions/e4aee9b6-58fb-457b-bdeb-dff17a40d870

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

lemma degreeUnionBranch43_780_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 33 10 degreeUnionState43_780 [10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_780_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_780_oai
