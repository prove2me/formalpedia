-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_930
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:43:05.468147+00:00
-- url     : https://prove2.me/submissions/49aa6527-00ca-4254-86ee-4e689d1ba361

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

lemma degreeUnionBranch62_930_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 25 11 degreeUnionState62_930 [11,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_930_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_930_oai
