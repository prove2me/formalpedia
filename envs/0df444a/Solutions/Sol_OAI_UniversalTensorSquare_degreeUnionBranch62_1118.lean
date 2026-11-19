-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1118
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:49:15.748574+00:00
-- url     : https://prove2.me/submissions/f704e89b-3ba1-4ed9-91a3-537f37635449

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

lemma degreeUnionBranch62_1118_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 28 10 degreeUnionState62_1118 [10,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1118_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1118_oai
