-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_676
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:33:24.58552+00:00
-- url     : https://prove2.me/submissions/a1b050e8-e94d-4f70-b81f-1be18aa8900c

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

lemma degreeUnionBranch62_676_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 21 8 degreeUnionState62_676 [8,10,11,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_676_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_676_oai
