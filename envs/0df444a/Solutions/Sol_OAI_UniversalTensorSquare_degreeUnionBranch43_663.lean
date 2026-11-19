-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_663
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:30:15.194394+00:00
-- url     : https://prove2.me/submissions/442e69c8-4c9c-4da3-b6cd-6e58f7baceeb

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

lemma degreeUnionBranch43_663_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 21 22 degreeUnionState43_663 [22] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_663_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_663_oai
