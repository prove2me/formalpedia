-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_396
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:42:45.329806+00:00
-- url     : https://prove2.me/submissions/40b1a78f-6950-411b-be69-46857d2c7156

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

lemma degreeUnionBranch62_396_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 42 6 degreeUnionState62_396 [6,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_396_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_396_oai
