-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1292
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T07:07:58.834732+00:00
-- url     : https://prove2.me/submissions/43978f2a-5fcf-454a-9101-d75662fe803a

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

lemma degreeUnionBranch62_1292_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 21 8 degreeUnionState62_1292 [8,9,10,14] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1292_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1292_oai
