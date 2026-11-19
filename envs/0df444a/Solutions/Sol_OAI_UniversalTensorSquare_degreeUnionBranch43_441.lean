-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_441
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:08:46.486079+00:00
-- url     : https://prove2.me/submissions/c2400b95-07e6-40f2-bc8c-c60e51976b12

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

lemma degreeUnionBranch43_441_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 10 degreeUnionState43_441 [10,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_441_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_441_oai
