-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_599
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:25:03.205604+00:00
-- url     : https://prove2.me/submissions/29da36b7-4bdf-426e-bbe1-c8dcb0492157

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

lemma degreeUnionBranch43_599_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 12 31 degreeUnionState43_599 [31] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_599_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_599_oai
