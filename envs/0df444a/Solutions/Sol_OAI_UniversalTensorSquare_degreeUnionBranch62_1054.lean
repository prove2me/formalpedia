-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1054
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:18:40.179469+00:00
-- url     : https://prove2.me/submissions/d70b3039-afd4-47d4-b8d6-9359f9a1de52

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

lemma degreeUnionBranch62_1054_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 26 5 degreeUnionState62_1054 [5,9,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1054_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1054_oai
