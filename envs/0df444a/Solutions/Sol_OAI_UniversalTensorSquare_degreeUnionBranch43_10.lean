-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:14:50.974712+00:00
-- url     : https://prove2.me/submissions/ffa0dbd6-10c7-4d75-98a8-d8ef05c90a31

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

lemma degreeUnionBranch43_10_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 36 7 degreeUnionState43_10 [7] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_10_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_10_oai
