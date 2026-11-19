-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_31
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:44:00.290258+00:00
-- url     : https://prove2.me/submissions/7fdb5a65-b266-43b6-9aae-5089e5158322

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

lemma degreeUnionBranch43_31_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 26 6 degreeUnionState43_31 [6,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_31_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_31_oai
