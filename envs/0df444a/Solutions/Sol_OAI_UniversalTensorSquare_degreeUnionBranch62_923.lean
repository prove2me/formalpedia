-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_923
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:31:38.609606+00:00
-- url     : https://prove2.me/submissions/7ea1ac93-6eb5-48c5-9024-c30df31a32ab

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

lemma degreeUnionBranch62_923_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 4 degreeUnionState62_923 [4,12,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_923_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_923_oai
