-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_246
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:35:26.192208+00:00
-- url     : https://prove2.me/submissions/c858f138-f9a0-453f-a19c-c1cca5b3c89a

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

lemma degreeUnionBranch43_246_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 20 9 degreeUnionState43_246 [9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_246_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_246_oai
