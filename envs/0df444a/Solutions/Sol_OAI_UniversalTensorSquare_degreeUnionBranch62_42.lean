-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_42
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:57:19.992172+00:00
-- url     : https://prove2.me/submissions/a737209c-3652-419c-886c-e5007ad54580

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

lemma degreeUnionBranch62_42_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 39 9 degreeUnionState62_42 [9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_42_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_42_oai
