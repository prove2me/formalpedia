-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_225
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:30:08.551796+00:00
-- url     : https://prove2.me/submissions/f1f035b5-b90c-44ae-bcf0-3c4dc7dd83d2

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

lemma degreeUnionBranch43_225_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 22 9 degreeUnionState43_225 [9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_225_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_225_oai
