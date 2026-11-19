-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_230
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:30:50.629244+00:00
-- url     : https://prove2.me/submissions/2178986f-fb6c-410f-9768-5ec007f7b95d

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

lemma degreeUnionBranch43_230_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 26 4 degreeUnionState43_230 [4,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_230_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_230_oai
