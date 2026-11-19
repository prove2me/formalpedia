-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_734
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:44:33.945388+00:00
-- url     : https://prove2.me/submissions/87a00dca-9b0e-4160-a31e-862f98e4d10c

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

lemma degreeUnionBranch43_734_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 38 5 degreeUnionState43_734 [5] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_734_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_734_oai
