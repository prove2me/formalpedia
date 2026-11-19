-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_348
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:48:55.278858+00:00
-- url     : https://prove2.me/submissions/40b86b77-54d4-43f3-a5b8-9c9513656c68

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

lemma degreeUnionBranch43_348_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 3 40 degreeUnionState43_348 [40] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_348_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_348_oai
