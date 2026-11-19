-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_102
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:45:49.937396+00:00
-- url     : https://prove2.me/submissions/7a73b8c2-916d-410c-bf62-b99b778550d5

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

lemma degreeUnionBranch39_102_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 19 20 degreeUnionState39_102 [20] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_102_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_102_oai
