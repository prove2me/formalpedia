-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_846
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:22:13.836075+00:00
-- url     : https://prove2.me/submissions/650efe0e-0ce9-47c6-87ba-236b4b84eecc

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

lemma degreeUnionBranch43_846_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 8 35 degreeUnionState43_846 [35] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_846_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_846_oai
