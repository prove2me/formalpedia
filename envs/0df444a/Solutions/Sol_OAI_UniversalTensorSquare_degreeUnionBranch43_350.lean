-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_350
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:52:52.353249+00:00
-- url     : https://prove2.me/submissions/f3063109-ca68-4ead-bf6f-8efe08d8e516

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

lemma degreeUnionBranch43_350_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 1 42 degreeUnionState43_350 [42] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_350_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_350_oai
