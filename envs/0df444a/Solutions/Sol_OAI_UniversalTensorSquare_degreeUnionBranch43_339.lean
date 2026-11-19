-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_339
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:47:55.562936+00:00
-- url     : https://prove2.me/submissions/0c632d2d-cc4c-4587-9a36-7f0269afc39c

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

lemma degreeUnionBranch43_339_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 12 31 degreeUnionState43_339 [31] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_339_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_339_oai
