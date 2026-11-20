-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_844
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:50:54.964155+00:00
-- url     : https://prove2.me/submissions/1bced2b9-d9a1-4a56-95f2-e91d497b237d

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

lemma degreeUnionBranch62_844_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 4 degreeUnionState62_844 [4,8,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_844_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_844_oai
