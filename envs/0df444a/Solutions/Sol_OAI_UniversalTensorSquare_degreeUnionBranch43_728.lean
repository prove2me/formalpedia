-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_728
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:41:21.007114+00:00
-- url     : https://prove2.me/submissions/e0b8c4fe-133e-4109-8fac-5f1596a604ad

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

lemma degreeUnionBranch43_728_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 4 39 degreeUnionState43_728 [39] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_728_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_728_oai
