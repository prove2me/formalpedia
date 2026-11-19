-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_34
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:48:01.958413+00:00
-- url     : https://prove2.me/submissions/1dec80b8-3477-47c9-b752-c795c8b75006

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

lemma degreeUnionBranch43_34_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 23 9 degreeUnionState43_34 [9,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_34_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_34_oai
