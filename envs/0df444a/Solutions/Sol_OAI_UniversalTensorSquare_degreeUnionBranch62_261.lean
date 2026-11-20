-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_261
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:26:26.328421+00:00
-- url     : https://prove2.me/submissions/b7a0f558-3b26-42da-bd50-704011800ca9

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_261_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 43 6 degreeUnionState62_261 [6,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_261_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_261_oai
