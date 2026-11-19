-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_412
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:02:55.238046+00:00
-- url     : https://prove2.me/submissions/f6c811fd-0716-40e5-a582-13d594f98e04

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

lemma degreeUnionBranch43_412_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 26 4 degreeUnionState43_412 [4,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_412_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_412_oai
