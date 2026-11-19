-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_288
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T02:01:19.13225+00:00
-- url     : https://prove2.me/submissions/a5a51ff6-bf64-4bc6-9579-7515f0615b75

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

lemma degreeUnionBranch39_288_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 20 19 degreeUnionState39_288 [19] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_288_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_288_oai
