-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_198
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:24:25.939391+00:00
-- url     : https://prove2.me/submissions/a69f1fff-29c0-4b2a-be6c-d9b93f63048d

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

lemma degreeUnionBranch43_198_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 20 5 degreeUnionState43_198 [5,9,9] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_198_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_198_oai
