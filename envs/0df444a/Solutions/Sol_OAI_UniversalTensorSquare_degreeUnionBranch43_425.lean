-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_425
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:04:19.178427+00:00
-- url     : https://prove2.me/submissions/471b9487-32ea-41c6-8c71-42df6187f0d8

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

lemma degreeUnionBranch43_425_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 23 6 degreeUnionState43_425 [6,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_425_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_425_oai
