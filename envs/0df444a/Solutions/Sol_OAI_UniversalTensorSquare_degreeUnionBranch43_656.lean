-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_656
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:29:26.564498+00:00
-- url     : https://prove2.me/submissions/6c8b71ea-e5d8-4e13-bb68-8f35e84e6e0c

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

lemma degreeUnionBranch43_656_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 28 15 degreeUnionState43_656 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_656_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_656_oai
