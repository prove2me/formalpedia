-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch43_733
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T03:41:52.178195+00:00
-- url     : https://prove2.me/submissions/e6acd6fc-526e-4a14-81cf-3b0843b923f0

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

lemma degreeUnionBranch43_733_oai : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 39 4 degreeUnionState43_733 [4] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch43_733_oai := @OAI.UniversalTensorSquare.degreeUnionBranch43_733_oai
