-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_281
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:35:22.39525+00:00
-- url     : https://prove2.me/submissions/be8c7251-21e3-40e6-93db-b78c72c2c2ae

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

lemma degreeUnionBranch62_281_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 27 6 degreeUnionState62_281 [6,8,8,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_281_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_281_oai
