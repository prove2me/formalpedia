-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1000
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:00:30.023057+00:00
-- url     : https://prove2.me/submissions/2f94588c-c2a7-4b6a-95b4-1c1f1cc1e417

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

lemma degreeUnionBranch62_1000_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 20 9 degreeUnionState62_1000 [9,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1000_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1000_oai
