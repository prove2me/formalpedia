-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_413
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:01.05144+00:00
-- url     : https://prove2.me/submissions/ee2b5eb5-2a4c-44b7-84e6-99ce4a71729d

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

lemma degreeUnionBranch43_413_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 25 5 degreeUnionState43_413 [5,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_413_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_413_oai
