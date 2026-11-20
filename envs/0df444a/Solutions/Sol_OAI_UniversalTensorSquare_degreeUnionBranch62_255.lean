-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_255
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:23:11.75187+00:00
-- url     : https://prove2.me/submissions/99374290-2fde-4ae6-b444-8fb8ada28a99

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

lemma degreeUnionBranch62_255_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 20 9 degreeUnionState62_255 [9,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_255_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_255_oai
