-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1185
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:22:21.717763+00:00
-- url     : https://prove2.me/submissions/2159f3f3-4666-45c9-a771-bdd7adb1efc1

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

lemma degreeUnionBranch62_1185_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 20 9 degreeUnionState62_1185 [9,10,10,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1185_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1185_oai
