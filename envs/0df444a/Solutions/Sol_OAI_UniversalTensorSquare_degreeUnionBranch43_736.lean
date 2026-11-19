-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_736
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:44:45.969173+00:00
-- url     : https://prove2.me/submissions/7aee89af-00f5-4b58-b781-73b96fb82c9f

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

lemma degreeUnionBranch43_736_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 36 7 degreeUnionState43_736 [7] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_736_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_736_oai
