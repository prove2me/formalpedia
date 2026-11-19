-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_298
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:04:53.789224+00:00
-- url     : https://prove2.me/submissions/e7ab2de5-8fd6-454f-994a-1d58794b1083

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

lemma degreeUnionBranch39_298_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 10 29 degreeUnionState39_298 [29] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_298_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_298_oai
