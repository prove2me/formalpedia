-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_302
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:05:23.237973+00:00
-- url     : https://prove2.me/submissions/1d5d0a78-33c8-48b0-a2a2-0954c9777297

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

lemma degreeUnionBranch39_302_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 6 33 degreeUnionState39_302 [33] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_302_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_302_oai
