-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_36
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:52:58.119456+00:00
-- url     : https://prove2.me/submissions/3a284bbd-efd1-4562-8ae2-7a857bbbd421

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

lemma degreeUnionBranch43_36_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 6 21 11 degreeUnionState43_36 [11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_36_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_36_oai
