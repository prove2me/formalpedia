-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_435
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:08:05.13628+00:00
-- url     : https://prove2.me/submissions/7c0b6e74-f1c6-4a03-a20f-e7121285d3c8

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

lemma degreeUnionBranch43_435_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 4 degreeUnionState43_435 [4,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_435_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_435_oai
