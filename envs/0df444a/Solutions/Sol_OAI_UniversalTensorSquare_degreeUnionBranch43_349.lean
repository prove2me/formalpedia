-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_349
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:49:01.104542+00:00
-- url     : https://prove2.me/submissions/102aa2c5-f99c-4eb1-a784-f819a81d616e

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

lemma degreeUnionBranch43_349_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 2 41 degreeUnionState43_349 [41] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_349_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_349_oai
