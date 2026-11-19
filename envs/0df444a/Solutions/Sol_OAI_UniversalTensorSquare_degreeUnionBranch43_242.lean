-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_242
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:35:02.019462+00:00
-- url     : https://prove2.me/submissions/04724430-869e-4d34-9d3f-fc737dbfec2e

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

lemma degreeUnionBranch43_242_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 24 5 degreeUnionState43_242 [5,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_242_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_242_oai
