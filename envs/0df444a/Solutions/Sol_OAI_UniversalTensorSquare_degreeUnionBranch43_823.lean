-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_823
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:16:30.990395+00:00
-- url     : https://prove2.me/submissions/24974f65-aebe-47f2-bdbd-508244f88d84

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

lemma degreeUnionBranch43_823_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 31 12 degreeUnionState43_823 [12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_823_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_823_oai
