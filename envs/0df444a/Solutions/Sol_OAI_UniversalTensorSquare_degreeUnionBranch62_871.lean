-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_871
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:02:28.146494+00:00
-- url     : https://prove2.me/submissions/b42010cc-4c91-4910-8b0a-2e1d7dd89f2e

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

lemma degreeUnionBranch62_871_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 26 4 degreeUnionState62_871 [4,9,9,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_871_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_871_oai
