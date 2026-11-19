-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_722
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:40:44.771718+00:00
-- url     : https://prove2.me/submissions/c7a10f4b-ecd3-439c-85f6-44c320190120

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

lemma degreeUnionBranch43_722_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 10 33 degreeUnionState43_722 [33] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_722_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_722_oai
