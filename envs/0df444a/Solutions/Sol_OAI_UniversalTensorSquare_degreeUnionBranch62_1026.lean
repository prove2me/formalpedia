-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1026
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:05:51.401896+00:00
-- url     : https://prove2.me/submissions/754ac5a4-5091-4e4e-9280-66842083c1b3

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

lemma degreeUnionBranch62_1026_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 4 degreeUnionState62_1026 [4,8,9,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1026_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1026_oai
