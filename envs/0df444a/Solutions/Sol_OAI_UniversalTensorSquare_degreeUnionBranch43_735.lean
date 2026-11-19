-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_735
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:44:39.974423+00:00
-- url     : https://prove2.me/submissions/ce8593ee-cb06-4704-b4f2-cc6b609e36c3

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

lemma degreeUnionBranch43_735_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 37 6 degreeUnionState43_735 [6] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_735_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_735_oai
