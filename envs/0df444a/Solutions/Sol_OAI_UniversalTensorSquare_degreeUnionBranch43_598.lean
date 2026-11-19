-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_598
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:24:57.297977+00:00
-- url     : https://prove2.me/submissions/7c6f798f-03ad-4a98-a9df-a08ae73fb25b

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

lemma degreeUnionBranch43_598_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 13 30 degreeUnionState43_598 [30] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_598_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_598_oai
