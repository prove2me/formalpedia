-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_231
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:30:56.476599+00:00
-- url     : https://prove2.me/submissions/b69063b4-7560-42df-9f25-c51c49427e02

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

lemma degreeUnionBranch43_231_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 5 degreeUnionState43_231 [5,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_231_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_231_oai
