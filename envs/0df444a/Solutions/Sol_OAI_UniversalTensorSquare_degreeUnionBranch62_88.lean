-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeUnionBranch62_88
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T13:08:13.267189+00:00
-- url     : https://prove2.me/submissions/e10443c8-e2cb-4bcb-8aeb-2884236b0433

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

lemma degreeUnionBranch62_88_oai : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 46 5 degreeUnionState62_88 [5,11] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeUnionBranch62_88_oai := @OAI.UniversalTensorSquare.degreeUnionBranch62_88_oai
