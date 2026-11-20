-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_439
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:10:19.578263+00:00
-- url     : https://prove2.me/submissions/1d0a60c6-d0e1-4fc1-bbd8-6f36d0245496

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

lemma degreeUnionBranch62_439_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 7 degreeUnionState62_439 [7,9,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_439_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_439_oai
