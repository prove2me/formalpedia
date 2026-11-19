-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1104
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:48:29.776581+00:00
-- url     : https://prove2.me/submissions/92db75be-fd49-4519-b747-262739f81d6d

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

lemma degreeUnionBranch62_1104_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 3 degreeUnionState62_1104 [3,8,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1104_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1104_oai
