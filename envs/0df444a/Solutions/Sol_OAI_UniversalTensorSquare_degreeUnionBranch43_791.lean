-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_791
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:06:01.919033+00:00
-- url     : https://prove2.me/submissions/47cd3227-ef2e-4782-9d0e-0128515c501e

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

lemma degreeUnionBranch43_791_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 22 21 degreeUnionState43_791 [21] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_791_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_791_oai
