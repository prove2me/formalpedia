-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_495
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:43:28.115945+00:00
-- url     : https://prove2.me/submissions/5fee784c-1e60-4960-aa66-653347b07656

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

lemma degreeUnionBranch62_495_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 11 degreeUnionState62_495 [11,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_495_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_495_oai
