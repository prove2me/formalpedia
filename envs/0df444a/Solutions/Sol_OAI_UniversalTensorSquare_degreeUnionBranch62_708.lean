-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_708
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T11:49:47.10885+00:00
-- url     : https://prove2.me/submissions/eaecc582-8ffc-4914-af53-2435605b2b2e

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

lemma degreeUnionBranch62_708_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 44 5 degreeUnionState62_708 [5,13] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_708_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_708_oai
