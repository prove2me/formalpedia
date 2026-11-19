-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_433
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:07:53.42709+00:00
-- url     : https://prove2.me/submissions/2ed4b8b5-f9ea-4f32-b75a-2fa7c254cb9c

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

lemma degreeUnionBranch43_433_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 15 14 degreeUnionState43_433 [14,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_433_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_433_oai
