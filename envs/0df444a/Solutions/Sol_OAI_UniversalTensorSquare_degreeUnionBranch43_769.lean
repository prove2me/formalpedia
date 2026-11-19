-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_769
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:55:17.998893+00:00
-- url     : https://prove2.me/submissions/7b8e3d80-7e23-47e8-9062-7bc8403fee57

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

lemma degreeUnionBranch43_769_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 3 40 degreeUnionState43_769 [40] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_769_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_769_oai
