-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_284
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:00:55.04478+00:00
-- url     : https://prove2.me/submissions/45f8b82a-6af8-483f-8137-f5fed29fd1d0

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

lemma degreeUnionBranch39_284_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 24 15 degreeUnionState39_284 [15] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_284_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_284_oai
