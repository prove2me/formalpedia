-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_287
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:01:13.079538+00:00
-- url     : https://prove2.me/submissions/c30af23f-3349-40e1-a70d-9a56e4338be7

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

lemma degreeUnionBranch39_287_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 21 18 degreeUnionState39_287 [18] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_287_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_287_oai
