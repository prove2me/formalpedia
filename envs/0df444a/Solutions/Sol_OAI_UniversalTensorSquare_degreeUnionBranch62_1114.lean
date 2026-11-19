-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1114
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:52:46.133068+00:00
-- url     : https://prove2.me/submissions/dc156c9d-28b6-4dc0-83de-d8ce952f42bc

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

lemma degreeUnionBranch62_1114_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 23 6 degreeUnionState62_1114 [6,9,12,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1114_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1114_oai
