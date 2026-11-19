-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_221
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:29:44.681199+00:00
-- url     : https://prove2.me/submissions/a8ed388b-bba5-4343-8e84-362064a63a3d

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

lemma degreeUnionBranch43_221_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 26 5 degreeUnionState43_221 [5,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_221_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_221_oai
