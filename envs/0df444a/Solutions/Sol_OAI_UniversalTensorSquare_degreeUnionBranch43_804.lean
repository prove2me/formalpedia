-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_804
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:11:02.153623+00:00
-- url     : https://prove2.me/submissions/cef5fa43-a27b-442a-9472-925f04f3d92a

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

lemma degreeUnionBranch43_804_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 9 34 degreeUnionState43_804 [34] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_804_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_804_oai
