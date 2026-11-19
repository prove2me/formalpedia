-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_828
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:16:49.529208+00:00
-- url     : https://prove2.me/submissions/cd46a664-0cc5-4aab-b76f-fd8638022f90

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

lemma degreeUnionBranch43_828_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 26 17 degreeUnionState43_828 [17] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_828_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_828_oai
