-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_353
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:49:31.286888+00:00
-- url     : https://prove2.me/submissions/a035abcc-e6fb-4cbc-800c-d42469f911cb

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

lemma degreeUnionBranch43_353_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 37 6 degreeUnionState43_353 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_353_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_353_oai
