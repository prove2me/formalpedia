-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_831
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:17:01.546447+00:00
-- url     : https://prove2.me/submissions/da3204cb-739f-44e3-b64d-1f396209378d

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

lemma degreeUnionBranch43_831_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 23 20 degreeUnionState43_831 [20] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_831_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_831_oai
