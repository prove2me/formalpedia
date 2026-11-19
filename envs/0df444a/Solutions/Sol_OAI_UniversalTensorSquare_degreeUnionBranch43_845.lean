-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_845
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:26:55.276878+00:00
-- url     : https://prove2.me/submissions/60d9d3b3-5e57-4bc0-b7aa-3663a7f74add

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

lemma degreeUnionBranch43_845_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 9 34 degreeUnionState43_845 [34] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_845_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_845_oai
