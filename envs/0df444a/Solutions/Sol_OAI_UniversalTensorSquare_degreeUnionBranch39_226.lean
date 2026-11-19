-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_226
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:59:47.912866+00:00
-- url     : https://prove2.me/submissions/571c2df2-6a05-4196-a97b-9d2e577d525c

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

lemma degreeUnionBranch39_226_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 35 4 degreeUnionState39_226 [4] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_226_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_226_oai
