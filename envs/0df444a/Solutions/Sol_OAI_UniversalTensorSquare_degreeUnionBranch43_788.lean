-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_788
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:05:50.004808+00:00
-- url     : https://prove2.me/submissions/9d33a151-5bd2-458a-9f4f-2042eacb1869

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

lemma degreeUnionBranch43_788_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 25 18 degreeUnionState43_788 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_788_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_788_oai
