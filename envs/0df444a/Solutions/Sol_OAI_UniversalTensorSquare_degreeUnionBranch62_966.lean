-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_966
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:43:33.333516+00:00
-- url     : https://prove2.me/submissions/fc952bad-55a3-4237-8516-1bf25745ef2e

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

lemma degreeUnionBranch62_966_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 44 7 degreeUnionState62_966 [7,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_966_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_966_oai
