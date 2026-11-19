-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_785
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:05:38.04198+00:00
-- url     : https://prove2.me/submissions/c8162e2c-aa8a-4362-82ac-62bbfac0a0c3

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

lemma degreeUnionBranch43_785_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 28 15 degreeUnionState43_785 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_785_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_785_oai
