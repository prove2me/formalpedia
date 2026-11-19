-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_195
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:07.870296+00:00
-- url     : https://prove2.me/submissions/09e1fe75-68f8-4998-8dc2-643ed4620da7

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

lemma degreeUnionBranch43_195_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 26 8 degreeUnionState43_195 [8,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_195_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_195_oai
