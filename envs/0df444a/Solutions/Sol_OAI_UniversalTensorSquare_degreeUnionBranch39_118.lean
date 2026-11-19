-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_118
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:50:17.676188+00:00
-- url     : https://prove2.me/submissions/b2d3c43c-f4d0-4bef-b976-92808c17632c

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

lemma degreeUnionBranch39_118_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 3 36 degreeUnionState39_118 [36] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_118_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_118_oai
