-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_1002
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:57:17.08717+00:00
-- url     : https://prove2.me/submissions/8c30b112-8ca9-40ca-ac47-c958c2ae61e2

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

lemma degreeUnionBranch62_1002_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 18 11 degreeUnionState62_1002 [11,11,11,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_1002_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_1002_oai
