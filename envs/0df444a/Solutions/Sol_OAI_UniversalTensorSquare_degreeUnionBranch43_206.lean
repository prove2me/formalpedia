-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_206
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:25:07.634678+00:00
-- url     : https://prove2.me/submissions/7715ef33-67a9-49b9-878e-e2ae4c5f4ca8

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

lemma degreeUnionBranch43_206_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 26 7 degreeUnionState43_206 [7,10] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_206_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_206_oai
