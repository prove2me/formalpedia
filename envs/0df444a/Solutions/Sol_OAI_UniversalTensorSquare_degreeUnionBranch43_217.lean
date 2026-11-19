-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_217
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:29:14.739089+00:00
-- url     : https://prove2.me/submissions/72a8b552-b60f-41c2-8d53-480b62358396

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

lemma degreeUnionBranch43_217_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 10 degreeUnionState43_217 [10,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_217_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_217_oai
