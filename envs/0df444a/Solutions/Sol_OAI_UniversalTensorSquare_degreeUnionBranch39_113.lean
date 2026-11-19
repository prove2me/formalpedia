-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_113
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:47:01.633195+00:00
-- url     : https://prove2.me/submissions/cc62af6e-e5cd-4814-9134-4235c5b6aaa7

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_113_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 8 31 degreeUnionState39_113 [31] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_113_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_113_oai
