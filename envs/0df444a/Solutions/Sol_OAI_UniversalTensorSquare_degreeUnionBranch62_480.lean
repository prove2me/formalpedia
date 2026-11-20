-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_480
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:38:18.945027+00:00
-- url     : https://prove2.me/submissions/727a0ff5-4471-4d70-9d1f-a07fe1d59630

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

lemma degreeUnionBranch62_480_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 28 9 degreeUnionState62_480 [9,11,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_480_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_480_oai
