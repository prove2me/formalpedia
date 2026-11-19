-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_398
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:58:13.957839+00:00
-- url     : https://prove2.me/submissions/d1947378-2d19-4262-8af7-d66841ed5159

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

lemma degreeUnionBranch43_398_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 23 9 degreeUnionState43_398 [9,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_398_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_398_oai
