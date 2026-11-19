-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_436
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:08:10.838958+00:00
-- url     : https://prove2.me/submissions/42c2244b-74f0-4dfe-91e7-a5cf801962a8

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

lemma degreeUnionBranch43_436_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 23 5 degreeUnionState43_436 [5,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_436_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_436_oai
