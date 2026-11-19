-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_440
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:08:40.679751+00:00
-- url     : https://prove2.me/submissions/567351c2-2db1-4fef-83a7-c86a1c6a1932

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

lemma degreeUnionBranch43_440_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 19 9 degreeUnionState43_440 [9,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_440_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_440_oai
