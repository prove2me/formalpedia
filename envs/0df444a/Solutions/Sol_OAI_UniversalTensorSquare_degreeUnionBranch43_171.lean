-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_171
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:19:31.741325+00:00
-- url     : https://prove2.me/submissions/d986299f-897c-4988-a1ea-5ec484e47c11

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

lemma degreeUnionBranch43_171_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 11 32 degreeUnionState43_171 [32] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_171_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_171_oai
