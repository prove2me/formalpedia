-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_786
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:05:44.079794+00:00
-- url     : https://prove2.me/submissions/8cdd0776-c4b9-430d-ab0d-ed2386594264

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

lemma degreeUnionBranch43_786_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 27 16 degreeUnionState43_786 [16] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_786_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_786_oai
