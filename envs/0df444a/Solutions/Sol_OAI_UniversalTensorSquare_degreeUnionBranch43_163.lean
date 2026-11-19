-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_163
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:18:45.010213+00:00
-- url     : https://prove2.me/submissions/60e9a117-b57e-4097-b8c3-120687d5b2c9

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

lemma degreeUnionBranch43_163_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 19 24 degreeUnionState43_163 [24] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_163_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_163_oai
