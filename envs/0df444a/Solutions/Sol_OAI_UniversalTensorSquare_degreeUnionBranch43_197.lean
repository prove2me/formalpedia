-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_197
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:20.015693+00:00
-- url     : https://prove2.me/submissions/b8671d00-a684-4bfd-9f84-933959cf4235

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

lemma degreeUnionBranch43_197_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 21 4 degreeUnionState43_197 [4,9,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_197_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_197_oai
