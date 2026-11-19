-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_222
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:56:39.097189+00:00
-- url     : https://prove2.me/submissions/b277184c-3b73-4c55-a1c8-d0943af6b9c1

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

lemma degreeUnionBranch39_222_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 3 36 degreeUnionState39_222 [36] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_222_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_222_oai
