-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch39_207
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T01:55:11.905522+00:00
-- url     : https://prove2.me/submissions/912d76fd-60ba-4a6a-b96a-d1e618963c83

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

lemma degreeUnionBranch39_207_oai : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 18 21 degreeUnionState39_207 [21] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch39_207_oai := @OAI.UniversalTensorSquare.degreeUnionBranch39_207_oai
