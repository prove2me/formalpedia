-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_414
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:06.969574+00:00
-- url     : https://prove2.me/submissions/e0013d83-c17a-40ac-93fe-ae4baeb4f93d

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

lemma degreeUnionBranch43_414_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 6 degreeUnionState43_414 [6,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_414_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_414_oai
