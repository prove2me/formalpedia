-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_223
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:29:56.445438+00:00
-- url     : https://prove2.me/submissions/b3870a30-abf3-42dd-bb9d-9e4b3b8f9a01

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

lemma degreeUnionBranch43_223_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 24 7 degreeUnionState43_223 [7,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_223_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_223_oai
