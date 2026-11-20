-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_623
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:16:29.422312+00:00
-- url     : https://prove2.me/submissions/9b0accfc-d80a-4021-9897-0f02a91cf6f9

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

lemma degreeUnionBranch62_623_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 6 degreeUnionState62_623 [6,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_623_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_623_oai
