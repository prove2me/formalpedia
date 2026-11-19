-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_79
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:10:44.126603+00:00
-- url     : https://prove2.me/submissions/fd8aeaaa-d5f9-40e5-ba5f-d83cd0174bf7

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

lemma degreeUnionBranch43_79_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 13 15 degreeUnionState43_79 [15,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_79_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_79_oai
