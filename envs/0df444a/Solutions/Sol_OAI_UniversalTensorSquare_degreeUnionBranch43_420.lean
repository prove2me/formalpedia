-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_420
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:03:49.145809+00:00
-- url     : https://prove2.me/submissions/25ff980f-c8ab-4f43-aa19-62fd10d841d7

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

lemma degreeUnionBranch43_420_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 18 12 degreeUnionState43_420 [12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_420_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_420_oai
