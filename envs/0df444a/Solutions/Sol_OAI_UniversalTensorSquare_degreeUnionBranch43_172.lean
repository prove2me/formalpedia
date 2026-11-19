-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_172
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:19:37.619593+00:00
-- url     : https://prove2.me/submissions/7ae33e22-688c-49f2-bb1e-25db10588cf2

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

lemma degreeUnionBranch43_172_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 10 33 degreeUnionState43_172 [33] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_172_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_172_oai
