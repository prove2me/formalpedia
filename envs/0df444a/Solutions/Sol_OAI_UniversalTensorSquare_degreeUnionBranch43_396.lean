-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_396
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:58:01.682981+00:00
-- url     : https://prove2.me/submissions/aa6bff13-3554-437e-9030-3c0bdb5da1f2

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

lemma degreeUnionBranch43_396_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 25 7 degreeUnionState43_396 [7,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_396_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_396_oai
