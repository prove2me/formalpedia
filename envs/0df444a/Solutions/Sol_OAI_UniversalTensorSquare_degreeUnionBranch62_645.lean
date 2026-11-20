-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_645
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:22:49.886747+00:00
-- url     : https://prove2.me/submissions/eb609a91-1c7d-4551-912b-b1e45af6c9f4

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

lemma degreeUnionBranch62_645_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 9 degreeUnionState62_645 [9,10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_645_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_645_oai
