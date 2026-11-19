-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_439
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:08:29.099786+00:00
-- url     : https://prove2.me/submissions/9e4b7db3-490c-4382-8b0d-8edb84c1437f

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

lemma degreeUnionBranch43_439_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 20 8 degreeUnionState43_439 [8,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_439_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_439_oai
