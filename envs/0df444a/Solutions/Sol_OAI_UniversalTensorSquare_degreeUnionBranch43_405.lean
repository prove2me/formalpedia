-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_405
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:59:07.607494+00:00
-- url     : https://prove2.me/submissions/c90f0c29-bf24-48f3-9e2f-8536e106fcf4

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

lemma degreeUnionBranch43_405_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 7 degreeUnionState43_405 [7,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_405_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_405_oai
