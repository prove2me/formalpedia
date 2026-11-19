-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_346
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:48:43.498577+00:00
-- url     : https://prove2.me/submissions/44d1e46f-f66c-4c4b-9243-ae09d8cbc639

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

lemma degreeUnionBranch43_346_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 5 38 degreeUnionState43_346 [38] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_346_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_346_oai
