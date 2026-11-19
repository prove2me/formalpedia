-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_782
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:00:43.72872+00:00
-- url     : https://prove2.me/submissions/67d2feca-0319-41f3-977f-3f7274b9c48b

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

lemma degreeUnionBranch43_782_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 31 12 degreeUnionState43_782 [12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_782_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_782_oai
