-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_222
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:29:50.589201+00:00
-- url     : https://prove2.me/submissions/d0645f8d-7fa4-4a7d-a999-b864395bf854

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

lemma degreeUnionBranch43_222_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 6 degreeUnionState43_222 [6,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_222_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_222_oai
