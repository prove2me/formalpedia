-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1212
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T06:35:22.502173+00:00
-- url     : https://prove2.me/submissions/8218651b-c416-4e03-9024-78e21f5b83b9

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

lemma degreeUnionBranch62_1212_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 6 degreeUnionState62_1212 [6,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1212_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1212_oai
