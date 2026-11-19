-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_385
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:54:15.609657+00:00
-- url     : https://prove2.me/submissions/193f7050-f34c-4aee-83df-407783d20ee8

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

lemma degreeUnionBranch43_385_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 29 4 degreeUnionState43_385 [4,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_385_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_385_oai
