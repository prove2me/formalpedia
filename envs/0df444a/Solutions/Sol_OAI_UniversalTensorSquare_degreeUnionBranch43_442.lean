-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_442
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:08:52.351065+00:00
-- url     : https://prove2.me/submissions/1de5412a-9017-4966-946c-d478f6858209

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

lemma degreeUnionBranch43_442_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 17 11 degreeUnionState43_442 [11,15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_442_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_442_oai
