-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_180
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:20:25.491872+00:00
-- url     : https://prove2.me/submissions/bd904930-d16a-4e41-91bd-230dda190ffe

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

lemma degreeUnionBranch43_180_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 2 41 degreeUnionState43_180 [41] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_180_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_180_oai
