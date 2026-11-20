-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_641
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:16:49.385066+00:00
-- url     : https://prove2.me/submissions/e3da37ba-7a3e-46c8-b301-2cf804c12e4e

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

lemma degreeUnionBranch62_641_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 25 5 degreeUnionState62_641 [5,10,10,12] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_641_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_641_oai
