-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_338
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:45:22.992149+00:00
-- url     : https://prove2.me/submissions/d2b47580-e6e7-4f86-b25a-13b55dfe1d72

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

lemma degreeUnionBranch43_338_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 13 30 degreeUnionState43_338 [30] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_338_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_338_oai
