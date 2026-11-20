-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_822
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:34:28.784449+00:00
-- url     : https://prove2.me/submissions/1d6ef10d-d2bc-4482-876d-64a49e4c429b

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

lemma degreeUnionBranch62_822_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 12 degreeUnionState62_822 [12,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_822_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_822_oai
