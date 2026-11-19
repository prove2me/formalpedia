-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1060
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:18:46.258195+00:00
-- url     : https://prove2.me/submissions/201b3807-f70e-402b-8d7b-55db6423020e

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

lemma degreeUnionBranch62_1060_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 3 degreeUnionState62_1060 [3,10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1060_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1060_oai
