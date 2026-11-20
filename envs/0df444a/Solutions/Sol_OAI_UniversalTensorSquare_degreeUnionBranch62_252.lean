-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_252
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T08:22:52.431199+00:00
-- url     : https://prove2.me/submissions/6d682465-852f-4da2-bc6e-c54ed0331afa

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

lemma degreeUnionBranch62_252_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 8 23 6 degreeUnionState62_252 [6,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_252_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_252_oai
