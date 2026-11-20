-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_820
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T12:29:42.68544+00:00
-- url     : https://prove2.me/submissions/1e641c6a-3781-4d7f-afd5-26d3df01d732

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

lemma degreeUnionBranch62_820_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 27 10 degreeUnionState62_820 [10,12,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_820_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_820_oai
