-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_996
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T14:00:49.882151+00:00
-- url     : https://prove2.me/submissions/c1be20b9-7e63-4ea0-8f44-36d4ac66c49b

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

lemma degreeUnionBranch62_996_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 24 5 degreeUnionState62_996 [5,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_996_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_996_oai
