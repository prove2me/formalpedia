-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_204
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:52:08.853543+00:00
-- url     : https://prove2.me/submissions/b26a6ebf-c33a-4240-91e3-1d17807752bb

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

lemma degreeUnionBranch39_204_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 21 18 degreeUnionState39_204 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_204_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_204_oai
