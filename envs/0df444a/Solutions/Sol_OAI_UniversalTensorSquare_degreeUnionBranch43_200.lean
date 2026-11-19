-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_200
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:43.555984+00:00
-- url     : https://prove2.me/submissions/aa98c088-248c-4b59-873b-dfff90a34df4

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

lemma degreeUnionBranch43_200_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 18 7 degreeUnionState43_200 [7,9,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_200_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_200_oai
