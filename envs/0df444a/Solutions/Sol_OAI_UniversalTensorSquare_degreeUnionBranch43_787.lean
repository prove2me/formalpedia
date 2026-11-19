-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_787
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:01:01.814189+00:00
-- url     : https://prove2.me/submissions/ce3feda7-cc9a-46b8-83ab-4ce283f76540

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

lemma degreeUnionBranch43_787_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 26 17 degreeUnionState43_787 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_787_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_787_oai
